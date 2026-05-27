import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairA0SourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairFixedWindow
import OSReconstruction.SCV.CompactSupportIntegralCLM
import OSReconstruction.SCV.LocalEOWSideContinuity

/-!
# OS-II Axis-Pair Product-Source Branch Limits

This companion records the first compact product-source form of the Section 4.3
side-boundary handoff.  The raw positive side CLM is evaluated on a product of
one-sided Laplace representatives, then the existing boundary source-current
theorem identifies the limit with the actual Malgrange-Zerner time-shell branch
integrated against the same compact product source.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators LineDeriv

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private theorem exists_schwartz_cutoff_real_eq_one_on_compact_subset_open_bounded
    {K U : Set ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (c R : ℝ) (hU_ball : U ⊆ Metric.ball c R) :
    ∃ χ : SchwartzMap ℝ ℂ,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : ℝ → ℂ) ⊆ U ∧
      HasCompactSupport (χ : ℝ → ℂ) := by
  classical
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let K₁ : Set (Fin 1 → ℝ) := e.symm '' K
  let U₁ : Set (Fin 1 → ℝ) := e ⁻¹' U
  have hK₁ : IsCompact K₁ := hK.image e.symm.continuous
  have hU₁ : IsOpen U₁ := hU.preimage e.continuous
  have hK₁U₁ : K₁ ⊆ U₁ := by
    intro y hy
    rcases hy with ⟨x, hxK, rfl⟩
    simpa [U₁] using hKU hxK
  rcases SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
      (m := 1) (K := K₁) (U := U₁) hK₁ hU₁ hK₁U₁ with
    ⟨ψ, hψ_one, hψ_supp⟩
  let χ : SchwartzMap ℝ ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) ψ
  have hχ_tsupport_preimage :
      tsupport (χ : ℝ → ℂ) ⊆
        (fun t : ℝ => e.symm t) ⁻¹'
          tsupport (ψ : (Fin 1 → ℝ) → ℂ) := by
    refine closure_minimal ?_ ?_
    · intro t ht
      exact subset_tsupport (ψ : (Fin 1 → ℝ) → ℂ) (by
        rw [Function.mem_support] at ht ⊢
        simpa [χ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using ht)
    · exact (isClosed_tsupport (ψ : (Fin 1 → ℝ) → ℂ)).preimage e.symm.continuous
  have hχ_supp_U : tsupport (χ : ℝ → ℂ) ⊆ U := by
    intro t ht
    have htψ := hχ_tsupport_preimage ht
    have htU₁ : e (e.symm t) ∈ U := hψ_supp htψ
    simpa using htU₁
  refine ⟨χ, ?_, hχ_supp_U, ?_⟩
  · intro x hxK
    have hxK₁ : e.symm x ∈ K₁ := ⟨x, hxK, rfl⟩
    simpa [χ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hψ_one (e.symm x) hxK₁
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall c R) ?_
    intro x hx
    have hxU : x ∈ U := hχ_supp_U (subset_tsupport (χ : ℝ → ℂ) hx)
    exact Metric.ball_subset_closedBall (hU_ball hxU)

omit [NeZero d] in
/-- Coordinatewise compact positive cutoffs for a compact subset of an
axis-pair half-window.

This is the product-cutoff selection used in the OS II V.2 smearing step: a
compact strict-positive carrier inside the smaller time-shell window admits
one-dimensional cutoffs whose product is one on the carrier and whose supports
remain in the larger Lemma 5.1 window. -/
theorem exists_axisPairWindow_productCutoffs_on_compact
    (ξ : Fin (d + 1) → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Fin (d + 1) → ℝ)}
    (hK : IsCompact K)
    (hK_pos : K ⊆ section43TimeStrictPositiveRegion (d + 1))
    (hK_window : K ⊆ osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2)) :
    ∃ χs : Fin (d + 1) → SchwartzMap ℝ ℂ,
      (∀ i : Fin (d + 1),
        tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) ∧
      (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) ∧
      (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
        ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) ∧
      (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
        ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) ∧
      (∀ τ ∈ K, section43TimeProductTensor χs τ = 1) := by
  classical
  let center : Fin (d + 1) → ℝ :=
    Fin.cases (ξ 0 / 2) (fun j : Fin d => ξ (Fin.succ j))
  let Kcoord : Fin (d + 1) → Set ℝ := fun i =>
    (fun τ : Fin (d + 1) → ℝ => τ i) '' K
  let Ucoord : Fin (d + 1) → Set ℝ := fun i =>
    {t : ℝ | 0 < t ∧ ‖((t - center i : ℝ) : ℂ)‖ < ρ}
  have hKcoord_compact : ∀ i, IsCompact (Kcoord i) := by
    intro i
    exact hK.image (continuous_apply i)
  have hUcoord_open : ∀ i, IsOpen (Ucoord i) := by
    intro i
    have hpos_open : IsOpen {t : ℝ | 0 < t} :=
      isOpen_lt continuous_const continuous_id
    have hrad_cont : Continuous (fun t : ℝ =>
        ‖((t - center i : ℝ) : ℂ)‖) := by
      fun_prop
    have hrad_open : IsOpen {t : ℝ | ‖((t - center i : ℝ) : ℂ)‖ < ρ} :=
      isOpen_lt hrad_cont continuous_const
    simpa [Ucoord, Set.setOf_and] using hpos_open.inter hrad_open
  have hKcoord_sub : ∀ i, Kcoord i ⊆ Ucoord i := by
    intro i t ht
    rcases ht with ⟨τ, hτK, rfl⟩
    have hhalf_lt : ρ / 2 < ρ := by linarith
    refine Fin.cases ?head ?tail i
    · have hτpos := hK_pos hτK 0
      have hτwin := hK_window hτK 0
      have hτwin_lt :
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ 0 : ℂ)‖ < ρ :=
        lt_trans hτwin hhalf_lt
      refine ⟨hτpos, ?_⟩
      simpa [center, osiiAxisPairTimeShellPerturbation] using hτwin_lt
    · intro j
      have hτpos := hK_pos hτK (Fin.succ j)
      have hτwin := hK_window hτK (Fin.succ j)
      have hτwin_lt :
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ (Fin.succ j) : ℂ)‖ < ρ :=
        lt_trans hτwin hhalf_lt
      refine ⟨hτpos, ?_⟩
      simpa [center, osiiAxisPairTimeShellPerturbation] using hτwin_lt
  have hUcoord_ball :
      ∀ i, Ucoord i ⊆ Metric.ball (center i) ρ := by
    intro i t ht
    have hrad : ‖((t - center i : ℝ) : ℂ)‖ < ρ := ht.2
    rw [Metric.mem_ball, Real.dist_eq]
    rwa [Complex.norm_real] at hrad
  have hcut_exists :
      ∀ i : Fin (d + 1), ∃ χ : SchwartzMap ℝ ℂ,
        (∀ t ∈ Kcoord i, χ t = 1) ∧
        tsupport (χ : ℝ → ℂ) ⊆ Ucoord i ∧
        HasCompactSupport (χ : ℝ → ℂ) := by
    intro i
    exact
      exists_schwartz_cutoff_real_eq_one_on_compact_subset_open_bounded
        (K := Kcoord i) (U := Ucoord i)
        (hKcoord_compact i) (hUcoord_open i) (hKcoord_sub i)
        (center i) ρ (hUcoord_ball i)
  choose χs hχ_one hχ_supp hχ_compact using hcut_exists
  have hχ_pos :
      ∀ i : Fin (d + 1),
        tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ) := by
    intro i t ht
    exact (hχ_supp i ht).1
  have hχ_head :
      ∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
        ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ := by
    intro t ht
    simpa [center] using (hχ_supp 0 ht).2
  have hχ_tail :
      ∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
        ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ := by
    intro j t ht
    simpa [center] using (hχ_supp (Fin.succ j) ht).2
  have hχ_one_K :
      ∀ τ ∈ K, section43TimeProductTensor χs τ = 1 := by
    intro τ hτK
    rw [section43TimeProductTensor, SchwartzMap.productTensor_apply]
    exact Finset.prod_eq_one (fun i _hi =>
      hχ_one i (τ i) ⟨τ, hτK, rfl⟩)
  exact ⟨χs, hχ_pos, hχ_compact, hχ_head, hχ_tail, hχ_one_K⟩

omit [NeZero d] in
/-- Axis-pair window form of the cutoff-selected supported product-source
extension.

The head cutoff is measured around `ξ⁰ / 2`, while the remaining cutoffs are
measured around the spatial/time-shell center coordinates of `ξ`.  These
coordinate support bounds put every product-source approximant inside the
Lemma 5.1 time-shell window, so the local source-side Banach-Steinhaus
extension applies to the original cutoff-selected test. -/
theorem section43_tendsto_timeSchwartz_of_axisPairWindow_productCutoff
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ}
    {T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ}
    (ξ : Fin (d + 1) → ℝ) (ρ : ℝ)
    (χs : Fin (d + 1) → SchwartzMap ℝ ℂ)
    (hχ_pos :
      ∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact :
      ∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_head :
      ∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
        ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ)
    (hχ_tail :
      ∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
        ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ)
    (F : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_one :
      ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
        section43TimeProductTensor χs τ = 1)
    (h_on_products :
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun a => Tseq a (section43TimeProductSource gs).f)
          l
          (nhds (T (section43TimeProductSource gs).f)))
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) φ‖ ≤ C) :
    Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  refine
    section43_tendsto_timeSchwartz_of_productCutoff_supportedProductSources
      (n := d + 1) (Tseq := Tseq) (T := T)
      (U := osiiAxisPairTimeShellWindow (d := d) ξ ρ)
      χs hχ_pos hχ_compact ?_ F hχ_one h_on_products
      h_pointwise_bounded
  intro τ hτ ν
  refine Fin.cases ?head ?tail ν
  · simpa [osiiAxisPairTimeShellPerturbation] using hχ_head (τ 0) (hτ 0)
  · intro j
    simpa [osiiAxisPairTimeShellPerturbation] using
      hχ_tail j (τ (Fin.succ j)) (hτ (Fin.succ j))

/-- Cutoff distribution generated by the local axis-pair time-shell branch.

The Lemma 5.1 branch is only used on its local real time-shell window.  A compact
cutoff whose support lies in that window turns the branch into an honest
continuous linear functional on finite-time Schwartz tests, and on tests where
the cutoff is one this CLM is integration against the uncut branch. -/
theorem exists_axisPair_timeShellBranch_cutoff_integralCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        ∃ L : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            L φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            (∀ τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ), χ τ = 1) →
              L φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ)) * φ τ) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hdiff, _hreal, _hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support
  let U : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρ
  let H : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have hU_open : IsOpen U := by
    simpa [U] using isOpen_osiiAxisPairTimeShellWindow (d := d) ξ (ρ := ρ)
  have hreal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp (continuous_apply ν)
  have hmaps :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        U
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ) := by
    intro τ hτ
    simpa [U, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hH_cont : ContinuousOn H U := by
    simpa [H, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hreal_cont.continuousOn hmaps
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      H χ hU_open hχ_compact (by simpa [U] using hχ_support) hH_cont with
    ⟨L, hL_cut, hL_one⟩
  refine ⟨L, ?_, ?_⟩
  · intro φ
    simpa [H, mul_assoc] using hL_cut φ
  · intro φ hχ_one
    simpa [H] using hL_one φ hχ_one

/-- Vector side-height continuity for the weighted axis-pair MZ branch.

This is the route-correct comparison between the holomorphic side boundary
value `τ + i y` and the zero-height real-edge branch integral.  It does not
identify the finite-height holomorphic side kernel with the real-shifted
source-current kernel; that comparison is only through the common boundary
limit. -/
theorem osiiAxisPair_weightedBranch_sideIntegral_tendsto_realEdge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (φ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (SCV.sideHeightSlice y τ) *
                φ τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                φ τ))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρbranch, C, hρbranch, hC, hdiff, _hreal, _hselector, _hbound⟩
  let ρ : ℝ := ρbranch / 3
  refine ⟨ρ, C, by dsimp [ρ]; linarith, hC, ?_⟩
  intro hφ_window
  let Y : Set (Fin (d + 1) → ℝ) := Metric.ball 0 ρ
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
  have hY_mem : Y ∈ 𝓝[Cside] (0 : Fin (d + 1) → ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hρ_pos)
  have hY0 : (0 : Fin (d + 1) → ℝ) ∈ Y := by
    simpa [Y] using hρ_pos
  have hmargin :
      ∀ y ∈ Y, ∀ τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ),
        SCV.sideHeightSlice y τ ∈
          osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch := by
    intro y hy τ hτ ν
    have hreal :
        ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ :=
      hφ_window hτ ν
    have hy_norm_lt : ‖((y ν : ℝ) : ℂ) * Complex.I‖ < ρ := by
      rw [norm_mul, Complex.norm_I, mul_one]
      have hy_norm : ‖y‖ < ρ := by
        simpa [Y, Metric.mem_ball, dist_zero_right] using hy
      exact lt_of_le_of_lt
        (by
          simpa [Complex.norm_real, Real.norm_eq_abs] using
            (norm_le_pi_norm y ν))
        hy_norm
    have hsplit :
        osiiAxisPairTimeShellPerturbationC (d := d) ξ
            (SCV.sideHeightSlice y τ) ν =
          (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ) +
            ((y ν : ℝ) : ℂ) * Complex.I := by
      refine Fin.cases ?_ ?_ ν
      · simp [SCV.sideHeightSlice, osiiAxisPairTimeShellPerturbation,
          osiiAxisPairTimeShellPerturbationC]
        ring
      · intro j
        simp [SCV.sideHeightSlice, osiiAxisPairTimeShellPerturbation,
          osiiAxisPairTimeShellPerturbationC]
        ring
    calc
      ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ
          (SCV.sideHeightSlice y τ) ν‖
          =
        ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ) +
          ((y ν : ℝ) : ℂ) * Complex.I‖ := by rw [hsplit]
      _ ≤ ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ +
          ‖((y ν : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ < ρbranch := by
        have hsum :
            ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ +
              ‖((y ν : ℝ) : ℂ) * Complex.I‖ < ρ + ρ :=
          add_lt_add hreal hy_norm_lt
        have hρρ : ρ + ρ < ρbranch := by
          dsimp [ρ]
          linarith
        exact lt_trans hsum hρρ
  have htend :=
    SCV.tendsto_sideIntegral_vector_nhdsWithin_zero
      (m := d + 1) (C := Cside) (Y := Y)
      (Ω := osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch)
      (F := osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ)
      (φ := φ)
      (by simpa using
        isOpen_osiiAxisPairTimeShellComplexWindow (d := d) ξ (ρ := ρbranch))
      (by
        simpa [osiiAxisPairWeightedTimeShellBranch] using hdiff.continuousOn)
      hφ_compact hY_mem hY0 hmargin
  have htarget_eq :
      (∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (SCV.sideHeightSlice 0 τ) *
            φ τ) =
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
            φ τ := by
    apply integral_congr_ae
    filter_upwards with τ
    congr 2
    ext ν
    simp [SCV.sideHeightSlice]
  simpa [htarget_eq] using htend

/-- Fixed-window local EOW branch representations for the actual axis-pair
weighted MZ branch.

This is the route-correct OS-II `(5.7)`--`(5.8)` consumer: the finite-height
side kernels are the holomorphic branch values `B(τ + i y)`, and their boundary
values are obtained by compact-support side-height continuity.  The theorem
does not identify those finite-height kernels with the real shifted semigroup
source current. -/
theorem osiiAxisPair_weightedBranch_fixedWindow_branchRepresentations
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cplus Cminus E : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin (d + 1) → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    {rψLarge rψOne ρchart rside δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ)
    (hδscale : 128 * σ ≤ δ)
    (hσρ : 4 * σ ≤ ρchart)
    (hcardσ : (Fintype.card (Fin (d + 1)) : ℝ) * (4 * σ) < rside)
    (hδρ : δ * 10 ≤ ρchart)
    (hδsum : (Fintype.card (Fin (d + 1)) : ℝ) * (δ * 10) < rside)
    (Ωplus Ωminus Dplus Dminus : Set (SCV.ComplexChartSpace (d + 1)))
    (Kreal : Set (Fin (d + 1) → ℝ))
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (χcoord : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (χU : SchwartzMap (SCV.ComplexChartSpace (d + 1)) ℂ)
    (χr χψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (x0 : Fin (d + 1) → ℝ)
    (ys : Fin (d + 1) → Fin (d + 1) → ℝ)
    (hli : LinearIndependent ℝ ys)
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus)
    (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (hDplus_Ω : Dplus ⊆ Ωplus)
    (hDminus_Ω : Dminus ⊆ Ωminus)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ))
    (hχcoord_compact :
      HasCompactSupport (χcoord : (Fin (d + 1) → ℝ) → ℂ))
    (hχ_support_E :
      tsupport
        (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
          (Fin (d + 1) → ℝ) → ℂ) ⊆ E)
    (hχcoord_one :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) (3 * ρchart),
        χcoord u = 1)
    (hplus_margin :
      ∀ y ∈ Cplus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin (d + 1) → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωplus)
    (hminus_margin :
      ∀ y ∈ Cminus, ∀ x ∈ tsupport
          (SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord :
            (Fin (d + 1) → ℝ) → ℂ),
        (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ SCV.TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ SCV.TubeDomain Cminus)
    (hDplus_window :
      Dplus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρchart))
    (hDminus_window :
      Dminus ⊆ SCV.localEOWAffineRealWindow x0 ys hli (2 * ρchart))
    (hsmall :
      ∀ t : Fin (d + 1) → ℝ, ‖t‖ ≤ rψLarge →
        ‖(SCV.localEOWRealLinearCLE ys hli).symm t‖ < ρchart)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωminus)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρchart,
        SCV.localEOWRealChart x0 ys u ∈ E)
    (hKreal_compact : IsCompact Kreal)
    (hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρchart,
        SCV.localEOWRealChart x0 ys u ∈ Kreal)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρchart,
        ∀ v : Fin (d + 1) → ℝ,
          (∀ j, 0 ≤ v j) →
          0 < ∑ j, v j →
          (∑ j, v j) < rside →
            SCV.localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρchart,
        ∀ v : Fin (d + 1) → ℝ,
          (∀ j, v j ≤ 0) →
          0 < ∑ j, -v j →
          (∑ j, -v j) < rside →
            SCV.localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : SCV.ComplexChartSpace (d + 1)) (8 * σ),
        χU z = 1)
    (hχr_one :
      ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) (2 * σ), χr t = 1)
    (hχr_support :
      tsupport (χr : (Fin (d + 1) → ℝ) → ℂ) ⊆
        Metric.closedBall 0 (4 * σ))
    (hχψ_one :
      ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψOne, χψ t = 1)
    (hχψ_support :
      tsupport (χψ : (Fin (d + 1) → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rψLarge)
    (hA4_one :
      ‖(SCV.localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne)
    (hrψ_one_large : rψOne ≤ rψLarge) :
    let B : SCV.ComplexChartSpace (d + 1) → ℂ :=
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ
    let Bcoord : SCV.ComplexChartSpace (d + 1) → ℂ :=
      fun ζ => B (SCV.localEOWChart x0 ys ζ)
    ∃ ρTS C : ℝ, 0 < ρTS ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρTS →
        (∀ x ∈ E, χbranch x = 1) →
        E ⊆ osiiAxisPairTimeShellWindow (d := d) ξ ρTS →
        Ωplus ⊆ osiiAxisPairTimeShellComplexWindow (d := d) ξ ρTS →
        Ωminus ⊆ osiiAxisPairTimeShellComplexWindow (d := d) ξ ρTS →
        ∃ Hdist : SchwartzMap (SCV.ComplexChartSpace (d + 1)) ℂ →L[ℂ] ℂ,
          SCV.RepresentsDistributionOnComplexDomain Hdist Bcoord
            (SCV.StrictPositiveImagBall (m := d + 1) σ) ∧
          SCV.RepresentsDistributionOnComplexDomain Hdist Bcoord
            (SCV.StrictNegativeImagBall (m := d + 1) σ)) := by
  classical
  intro B Bcoord
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρlocal, C, hρlocal, hC, hdiff, _hreal, _hselector, _hbound⟩
  let ρTS : ℝ := ρlocal / 3
  have hρTS : 0 < ρTS := by
    dsimp [ρTS]
    linarith
  have hρTS_lt : ρTS < ρlocal := by
    dsimp [ρTS]
    linarith
  refine ⟨ρTS, C, hρTS, hC, ?_⟩
  intro hχbranch_support hχbranch_one_E hE_window hΩplus_sub hΩminus_sub
  let Hreal : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    B (fun ν : Fin (d + 1) => (τ ν : ℂ))
  let Ureal : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρlocal
  have hUreal_open : IsOpen Ureal := by
    simpa [Ureal] using isOpen_osiiAxisPairTimeShellWindow (d := d) ξ
      (ρ := ρlocal)
  have hχbranch_support_local :
      tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆ Ureal := by
    intro τ hτ ν
    exact lt_trans (hχbranch_support hτ ν) hρTS_lt
  have hreal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp
      (continuous_apply ν)
  have hmaps_real :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        Ureal
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρlocal) := by
    intro τ hτ
    simpa [Ureal, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hHreal_cont : ContinuousOn Hreal Ureal := by
    simpa [Hreal, B, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hreal_cont.continuousOn hmaps_real
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      Hreal χbranch hUreal_open hχbranch_compact hχbranch_support_local
      hHreal_cont with
    ⟨Tchart, _hTchart_cut, hTchart_one⟩
  have hB_diff_plus : DifferentiableOn ℂ B Ωplus := by
    refine hdiff.mono ?_
    intro z hz ν
    exact lt_trans (hΩplus_sub hz ν) hρTS_lt
  have hB_diff_minus : DifferentiableOn ℂ B Ωminus := by
    refine hdiff.mono ?_
    intro z hz ν
    exact lt_trans (hΩminus_sub hz ν) hρTS_lt
  have hside_bv :
      ∀ (Cside : Set (Fin (d + 1) → ℝ)),
        ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
          HasCompactSupport (φ : (Fin (d + 1) → ℝ) → ℂ) →
          tsupport (φ : (Fin (d + 1) → ℝ) → ℂ) ⊆ E →
            Tendsto
              (fun y : Fin (d + 1) → ℝ =>
                ∫ x : Fin (d + 1) → ℝ,
                  B (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
                    Complex.I) * φ x)
              (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
              (nhds ((Tchart.restrictScalars ℝ) φ)) := by
    intro Cside φ hφ_compact hφ_support
    let Y : Set (Fin (d + 1) → ℝ) := Metric.ball 0 ρTS
    have hY_mem : Y ∈ 𝓝[Cside] (0 : Fin (d + 1) → ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hρTS)
    have hY0 : (0 : Fin (d + 1) → ℝ) ∈ Y := by
      simpa [Y] using hρTS
    have hmargin :
        ∀ y ∈ Y, ∀ x ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ),
          SCV.sideHeightSlice y x ∈
            osiiAxisPairTimeShellComplexWindow (d := d) ξ ρlocal := by
      intro y hy x hx ν
      have hx_window :
          x ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρTS :=
        hE_window (hφ_support hx)
      have hreal :
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ x ν : ℂ)‖ < ρTS :=
        hx_window ν
      have hy_norm_lt : ‖((y ν : ℝ) : ℂ) * Complex.I‖ < ρTS := by
        rw [norm_mul, Complex.norm_I, mul_one]
        have hy_norm : ‖y‖ < ρTS := by
          simpa [Y, Metric.mem_ball, dist_zero_right] using hy
        exact lt_of_le_of_lt
          (by
            simpa [Complex.norm_real, Real.norm_eq_abs] using
              (norm_le_pi_norm y ν))
          hy_norm
      have hsplit :
          osiiAxisPairTimeShellPerturbationC (d := d) ξ
              (SCV.sideHeightSlice y x) ν =
            (osiiAxisPairTimeShellPerturbation (d := d) ξ x ν : ℂ) +
              ((y ν : ℝ) : ℂ) * Complex.I := by
        refine Fin.cases ?_ ?_ ν
        · simp [SCV.sideHeightSlice, osiiAxisPairTimeShellPerturbation,
            osiiAxisPairTimeShellPerturbationC]
          ring
        · intro j
          simp [SCV.sideHeightSlice, osiiAxisPairTimeShellPerturbation,
            osiiAxisPairTimeShellPerturbationC]
          ring
      calc
        ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ
            (SCV.sideHeightSlice y x) ν‖
            =
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ x ν : ℂ) +
            ((y ν : ℝ) : ℂ) * Complex.I‖ := by rw [hsplit]
        _ ≤
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ x ν : ℂ)‖ +
            ‖((y ν : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
        _ < ρlocal := by
          have hsum :
              ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ x ν : ℂ)‖ +
                ‖((y ν : ℝ) : ℂ) * Complex.I‖ < ρTS + ρTS :=
            add_lt_add hreal hy_norm_lt
          have htwice : ρTS + ρTS < ρlocal := by
            dsimp [ρTS]
            linarith
          exact lt_trans hsum htwice
    have hB_cont_local :
        ContinuousOn B
          (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρlocal) := by
      simpa [B, osiiAxisPairWeightedTimeShellBranch] using hdiff.continuousOn
    have htend :=
      SCV.tendsto_sideIntegral_vector_nhdsWithin_zero
        (m := d + 1) (C := Cside) (Y := Y)
        (Ω := osiiAxisPairTimeShellComplexWindow (d := d) ξ ρlocal)
        B φ
        (by
          simpa using
            (isOpen_osiiAxisPairTimeShellComplexWindow (d := d) ξ
              (ρ := ρlocal)))
        hB_cont_local hφ_compact hY_mem hY0 hmargin
    have htarget :
        (Tchart.restrictScalars ℝ) φ =
          ∫ x : Fin (d + 1) → ℝ,
            B (fun ν : Fin (d + 1) => (x ν : ℂ)) * φ x := by
      change Tchart φ =
        ∫ x : Fin (d + 1) → ℝ,
          B (fun ν : Fin (d + 1) => (x ν : ℂ)) * φ x
      simpa [Hreal] using hTchart_one φ (by
        intro x hx
        exact hχbranch_one_E x (hφ_support hx))
    have hsource_eq :
        (fun y : Fin (d + 1) → ℝ =>
          ∫ x : Fin (d + 1) → ℝ,
            B (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
              Complex.I) * φ x)
          =
        (fun y : Fin (d + 1) → ℝ =>
          ∫ x : Fin (d + 1) → ℝ,
            B (SCV.sideHeightSlice y x) * φ x) := by
      funext y
      apply integral_congr_ae
      filter_upwards with x
      congr 2
    have hzero_eq :
        (∫ x : Fin (d + 1) → ℝ,
            B (SCV.sideHeightSlice 0 x) * φ x) =
          ∫ x : Fin (d + 1) → ℝ,
            B (fun ν : Fin (d + 1) => (x ν : ℂ)) * φ x := by
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ext ν
      simp [SCV.sideHeightSlice]
    rw [hsource_eq]
    simpa [hzero_eq, htarget] using htend
  rcases
    SCV.localEOWSliceCLMs_from_preparedDomains
      (m := d + 1) (Cplus := Cplus) (Cminus := Cminus) (E := E)
      (rψ := rψLarge) (ρ := ρchart)
      Ωplus Ωminus Dplus Dminus B B Tchart x0 ys hli χcoord
      hΩplus_open hΩminus_open hB_diff_plus hB_diff_minus
      hχcoord_compact hχ_support_E hχcoord_one hplus_margin
      hminus_margin hDplus_sub hDminus_sub hDplus_window hDminus_window
      hsmall (hside_bv Cplus) (hside_bv Cminus) with
    ⟨Tplus, Tminus, hplus_eval, hminus_eval, hplus_limit, hminus_limit⟩
  let χaff : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    SCV.localEOWAffineTestPushforwardCLM x0 ys hli χcoord
  let Tcut : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    Tchart.comp (SchwartzMap.smulLeftCLM ℂ (χaff : (Fin (d + 1) → ℝ) → ℂ))
  have hplus_limit_cut :
      ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        Tendsto (fun y => Tplus y φ) (𝓝[Cplus] (0 : Fin (d + 1) → ℝ))
          (nhds ((Tcut.restrictScalars ℝ) φ)) := by
    intro φ
    simpa [Tcut, χaff] using hplus_limit φ
  have hminus_limit_cut :
      ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        Tendsto (fun y => Tminus y φ) (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (nhds ((Tcut.restrictScalars ℝ) φ)) := by
    intro φ
    simpa [Tcut, χaff] using hminus_limit φ
  simpa [Bcoord] using
    SCV.regularizedLocalEOW_branchRepresentations_from_fixedWindowScale
      (m := d + 1) (Cplus := Cplus) (Cminus := Cminus)
      (rψLarge := rψLarge) (rψOne := rψOne) (ρ := ρchart)
      (r := rside) (δ := δ) (σ := σ)
      (hm := Nat.succ_pos d) hδ hσ hδscale hσρ hcardσ
      Ωplus Ωminus Dplus Dminus E Kreal hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open hDplus_Ω hDminus_Ω
      B B hB_diff_plus hB_diff_minus hplus_margin_closed
      hminus_margin_closed hDplus_sub hDminus_sub Tplus Tminus Tcut
      hplus_eval hminus_eval hplus_limit_cut hminus_limit_cut x0 ys hli
      hδρ hδsum hE_mem hKreal_compact hKreal_mem hplus hminus
      χU χr χψ hχU_one hχr_one hχr_support hχψ_one hχψ_support
      hA4_one hrψ_one_large

/-- Cutoff distribution generated by the positive finite-height shifted
axis-pair time-shell branch.

This is the moving source-side companion to
`exists_axisPair_timeShellBranch_cutoff_integralCLM`: if the head-shifted
support remains in the Lemma 5.1 time-shell window, the shifted branch defines
a genuine Schwartz CLM after multiplication by the same compact cutoff. -/
theorem exists_axisPair_positiveShifted_timeShellBranch_cutoff_integralCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ))
    (y : Fin (d + 1) → ℝ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ((∀ τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ),
        (fun ν : Fin (d + 1) =>
          if ν = 0 then τ 0 + y 0 else τ ν) ∈
            osiiAxisPairTimeShellWindow (d := d) ξ ρ) →
        ∃ L : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            L φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                  φ τ) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            (∀ τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ), χ τ = 1) →
              L φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
                    φ τ) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hdiff, _hreal, _hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support
  let shiftC : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℂ := fun τ ν =>
    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)
  let U : Set (Fin (d + 1) → ℝ) :=
    shiftC ⁻¹' osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ
  let H : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T ξ (shiftC τ)
  have hshift_cont : Continuous shiftC := by
    exact continuous_pi fun ν =>
      Fin.cases
        (by
          simp [shiftC]
          fun_prop)
        (fun j => by
          simp [shiftC]
          fun_prop)
        ν
  have hU_open : IsOpen U := by
    exact (isOpen_osiiAxisPairTimeShellComplexWindow (d := d) ξ (ρ := ρ)).preimage
      hshift_cont
  have hχU : tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆ U := by
    intro τ hτ
    have hτ := hχ_support τ hτ
    simpa [U, shiftC, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hmaps :
      Set.MapsTo shiftC U
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ) := by
    intro τ hτ
    exact hτ
  have hH_cont : ContinuousOn H U := by
    simpa [H, shiftC, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hshift_cont.continuousOn hmaps
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      H χ hU_open hχ_compact hχU hH_cont with
    ⟨L, hL_cut, hL_one⟩
  refine ⟨L, ?_, ?_⟩
  · intro φ
    simpa [H, shiftC, mul_assoc] using hL_cut φ
  · intro φ hχ_one
    simpa [H, shiftC] using hL_one φ hχ_one

/-- Single-split real-time specialization of the expanded OS semigroup branch. -/
private theorem OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_ofReal_eq_schwinger
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    {t : ℝ} (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) (t : ℂ) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
  rw [OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
    (d := d) (OS := OS) (lgc := lgc)
    (F := PositiveTimeBorchersSequence.single n f hf_ord)
    (G := PositiveTimeBorchersSequence.single r g hg_ord)
    (hG_compact := by
      intro k
      by_cases hk : k = r
      · subst hk
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          hg_compact
      · have hzero :
          ((((PositiveTimeBorchersSequence.single r g hg_ord :
              PositiveTimeBorchersSequence d) :
              BorchersSequence d).funcs k : SchwartzNPoint d k) :
            NPointDomain d k → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hk]
        rw [hzero]
        simpa using (HasCompactSupport.zero :
          HasCompactSupport (0 : NPointDomain d k → ℂ)))
    (t := t) ht]
  simp only [PositiveTimeBorchersSequence.single_toBorchersSequence]
  have hshift_single :
      ∀ k,
        (timeShiftBorchers (d := d) t (BorchersSequence.single r g)).funcs k =
          (BorchersSequence.single r
            (timeShiftSchwartzNPoint (d := d) t g)).funcs k := by
    intro k
    by_cases hk : k = r
    · subst hk
      simp [BorchersSequence.single]
    · simp [BorchersSequence.single, hk]
  calc
    OSInnerProduct d OS.S (BorchersSequence.single n f)
        (timeShiftBorchers (d := d) t (BorchersSequence.single r g)) =
      OSInnerProduct d OS.S (BorchersSequence.single n f)
        (BorchersSequence.single r
          (timeShiftSchwartzNPoint (d := d) t g)) := by
          exact OSInnerProduct_congr_right d OS.S OS.E0_linear
            (BorchersSequence.single n f)
            (timeShiftBorchers (d := d) t (BorchersSequence.single r g))
            (BorchersSequence.single r
              (timeShiftSchwartzNPoint (d := d) t g))
            hshift_single
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) := by
          simpa using
            (OSInnerProduct_single_single d OS.S OS.E0_linear n r f
              (timeShiftSchwartzNPoint (d := d) t g))

/-- Positive finite-height product-source identity with the actual shifted
axis-pair branch.

The raw side current first selects the real semigroup value at `τ⁰ + y⁰`.
When the shifted real shell point remains in the Lemma 5.1 window, the
weighted MZ branch at that shifted point is the same scalar. -/
theorem osiiAxisPair_positiveSide_timeProductTensor_eq_shiftedBranch_sideWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ {y : Fin (d + 1) → ℝ}, 0 < y 0 →
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        (∀ τ : Fin (d + 1) → ℝ,
          τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) →
          (fun ν : Fin (d + 1) =>
            if ν = 0 then τ 0 + y 0 else τ ν) ∈
              osiiAxisPairTimeShellWindow (d := d) ξ ρ) →
        osiiAxisPairPositiveSideCLMC (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) y
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro y hy gs hshift
  rw [osiiAxisPairPositiveSideCLMC_timeProductTensor_finiteHeight
    (d := d) OS lgc
    (PositiveTimeBorchersSequence.single n f hf_ord)
    (PositiveTimeBorchersSequence.single r g hg_ord) hy gs]
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτ :
      τ ∈ tsupport
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
  · have hτ_pos : 0 < τ 0 := (section43TimeProductSource gs).positive hτ 0
    have ht : 0 < τ 0 + y 0 := add_pos hτ_pos hy
    have hbranch :=
      hreal (fun ν : Fin (d + 1) =>
          if ν = 0 then τ 0 + y 0 else τ ν)
        (hshift τ hτ)
    have hsemigroup :
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            (((τ 0 + y 0 : ℝ) : ℂ)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0 + y 0) g))) :=
      OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_ofReal_eq_schwinger
        (d := d) OS lgc f hf_ord g hg_ord hg_compact ht
    have hbranch_semigroup :
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) =>
              ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) =
          OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            (((τ 0 + y 0 : ℝ) : ℂ)) := by
      rw [hbranch]
      simpa using hsemigroup.symm
    rw [hbranch_semigroup]
  · have hzero : (section43TimeProductSource gs).f τ = 0 :=
      image_eq_zero_of_notMem_tsupport hτ
    simp [hzero]

/-- Lower finite-height product-source identity with the actual shifted
axis-pair branch.  The positive semigroup height is `-y⁰`. -/
theorem osiiAxisPair_lowerSide_timeProductTensor_eq_shiftedBranch_sideWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ {y : Fin (d + 1) → ℝ}, y 0 < 0 →
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        (∀ τ : Fin (d + 1) → ℝ,
          τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ) →
          (fun ν : Fin (d + 1) =>
            if ν = 0 then τ 0 + (-y 0) else τ ν) ∈
              osiiAxisPairTimeShellWindow (d := d) ξ ρ) →
        osiiAxisPairLowerSideCLMC (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) y
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro y hy gs hshift
  rw [osiiAxisPairLowerSideCLMC_timeProductTensor_finiteHeight
    (d := d) OS lgc
    (PositiveTimeBorchersSequence.single n f hf_ord)
    (PositiveTimeBorchersSequence.single r g hg_ord) hy gs]
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτ :
      τ ∈ tsupport
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
  · have hτ_pos : 0 < τ 0 := (section43TimeProductSource gs).positive hτ 0
    have hheight : 0 < -y 0 := neg_pos.mpr hy
    have ht : 0 < τ 0 + (-y 0) := add_pos hτ_pos hheight
    have hbranch :=
      hreal (fun ν : Fin (d + 1) =>
          if ν = 0 then τ 0 + (-y 0) else τ ν)
        (hshift τ hτ)
    have hsemigroup :
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            (((τ 0 + (-y 0) : ℝ) : ℂ)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0 + (-y 0)) g))) :=
      OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_ofReal_eq_schwinger
        (d := d) OS lgc f hf_ord g hg_ord hg_compact ht
    have hbranch_semigroup :
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) =>
              ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) =
          OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord)
            (((τ 0 + (-y 0) : ℝ) : ℂ)) := by
      rw [hbranch]
      simpa using hsemigroup.symm
    rw [hbranch_semigroup]
  · have hzero : (section43TimeProductSource gs).f τ = 0 :=
      image_eq_zero_of_notMem_tsupport hτ
    simp [hzero]

omit [NeZero d] in
/-- A time-shell point in a half-radius window remains in the full window after
a nonnegative time-coordinate shift smaller than the half-radius. -/
theorem osiiAxisPairTimeShellWindow_shift_time_mem
    (ξ τ : Fin (d + 1) → ℝ) {ρ η : ℝ} (hρ : 0 < ρ)
    (hτ : τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2))
    (hη_nonneg : 0 ≤ η) (hη : η < ρ / 2) :
    (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + η else τ ν) ∈
      osiiAxisPairTimeShellWindow (d := d) ξ ρ := by
  intro ν
  rcases Fin.eq_zero_or_eq_succ ν with rfl | ⟨j, rfl⟩
  · have hτ0 : ‖((τ 0 - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ / 2 := by
      simpa [osiiAxisPairTimeShellWindow, osiiAxisPairTimeShellPerturbation]
        using hτ 0
    have hη_norm : ‖((η : ℝ) : ℂ)‖ < ρ / 2 := by
      simpa [Real.norm_of_nonneg hη_nonneg] using hη
    have hsum :
        ‖((τ 0 - ξ 0 / 2 : ℝ) : ℂ) + ((η : ℝ) : ℂ)‖ < ρ := by
      calc
        ‖((τ 0 - ξ 0 / 2 : ℝ) : ℂ) + ((η : ℝ) : ℂ)‖
            ≤ ‖((τ 0 - ξ 0 / 2 : ℝ) : ℂ)‖ + ‖((η : ℝ) : ℂ)‖ :=
              norm_add_le _ _
        _ < ρ / 2 + ρ / 2 := add_lt_add hτ0 hη_norm
        _ = ρ := by ring
    simpa [osiiAxisPairTimeShellWindow, osiiAxisPairTimeShellPerturbation,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  · have hτν :
        ‖((osiiAxisPairTimeShellPerturbation (d := d) ξ τ
            (Fin.succ j) : ℝ) : ℂ)‖ < ρ / 2 := by
      simpa only using hτ (Fin.succ j)
    have hhalf_lt : ρ / 2 < ρ := by linarith
    have hlt :
        ‖((osiiAxisPairTimeShellPerturbation (d := d) ξ τ
            (Fin.succ j) : ℝ) : ℂ)‖ < ρ :=
      lt_trans hτν hhalf_lt
    simpa [osiiAxisPairTimeShellWindow, osiiAxisPairTimeShellPerturbation]
      using hlt

omit [NeZero d] in
/-- Positive-side collar: if a test support lies in a half-radius time-shell
window, then for sufficiently small positive side height the shifted support
lies in the full window. -/
theorem osiiAxisPair_eventually_positive_shifted_tsupport_mem_timeShellWindow
    (ξ : Fin (d + 1) → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (F : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hF_support :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2))
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    ∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
      ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
        (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + y 0 else τ ν) ∈
          osiiAxisPairTimeShellWindow (d := d) ξ ρ := by
  have hsmall :
      {y : Fin (d + 1) → ℝ | y 0 < ρ / 2} ∈
        𝓝[Cside] (0 : Fin (d + 1) → ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds (by
      apply IsOpen.mem_nhds
      · exact isOpen_lt (continuous_apply 0) continuous_const
      · simpa using (half_pos hρ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hyC hy_small τ hτ
  have hypos : 0 < y 0 := hCside_pos hyC
  exact
    osiiAxisPairTimeShellWindow_shift_time_mem
      (d := d) ξ τ hρ (hF_support hτ) (le_of_lt hypos) hy_small

/-- Positive side-cone eventual product-source equality with the shifted branch.

If the compact product-source support lies in the half-radius time-shell
window, then along the positive side cone the finite-height shifted shell
points eventually lie in the full Lemma 5.1 window, so the raw side current is
eventually the shifted weighted-branch product-source integral. -/
theorem osiiAxisPair_positiveSide_timeProductTensor_eventually_eq_shiftedBranch_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        ∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
          osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ := by
  classical
  intro F G
  rcases
    osiiAxisPair_positiveSide_timeProductTensor_eq_shiftedBranch_sideWindow
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hshifted⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gs hgs_window
  have hsmall :
      {y : Fin (d + 1) → ℝ | y 0 < ρ / 2} ∈
        𝓝[Cside] (0 : Fin (d + 1) → ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds (by
      apply IsOpen.mem_nhds
      · exact isOpen_lt (continuous_apply 0) continuous_const
      · simpa using (half_pos hρ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hyC hy_small
  have hypos : 0 < y 0 := hCside_pos hyC
  exact hshifted hypos gs (by
    intro τ hτ
    exact
      osiiAxisPairTimeShellWindow_shift_time_mem
        (d := d) ξ τ hρ (hgs_window hτ) (le_of_lt hypos) hy_small)

/-- Lower side-cone eventual product-source equality with the shifted branch. -/
theorem osiiAxisPair_lowerSide_timeProductTensor_eventually_eq_shiftedBranch_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        ∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
          osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
            (section43TimeProductTensor
              (fun i : Fin (d + 1) =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ := by
  classical
  intro F G
  rcases
    osiiAxisPair_lowerSide_timeProductTensor_eq_shiftedBranch_sideWindow
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hshifted⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gs hgs_window
  have hsmall :
      {y : Fin (d + 1) → ℝ | -y 0 < ρ / 2} ∈
        𝓝[Cminus] (0 : Fin (d + 1) → ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds (by
      apply IsOpen.mem_nhds
      · exact isOpen_lt ((continuous_apply 0).neg) continuous_const
      · simpa using (half_pos hρ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hyC hy_small
  have hyneg : y 0 < 0 := hCminus_neg hyC
  have hheight : 0 < -y 0 := neg_pos.mpr hyneg
  exact hshifted hyneg gs (by
    intro τ hτ
    exact
      osiiAxisPairTimeShellWindow_shift_time_mem
        (d := d) ξ τ hρ (hgs_window hτ) (le_of_lt hheight) hy_small)

/-- Positive side-cone product-source branch-integral limit.

On a common Lemma 5.1 time-shell window, the raw positive side CLM applied to a
product of one-sided Laplace representatives tends to the compact product-source
integral of the selected axis-pair MZ branch.  This is the product-source
version of the OS II `(5.7)`--`(5.8)` side handoff; it uses the boundary
source-current comparison rather than treating the head-restricted raw CLM as an
ordinary full real-slice density. -/
theorem osiiAxisPair_positiveSide_timeProductTensor_tendsto_branchIntegral_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
              (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ)) := by
  classical
  intro F G
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρb, Cb, hρb, hCb, hboundary_product⟩
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρr, Cr, hρr, hCr, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨min ρb ρr, Cb + Cr, lt_min hρb hρr, add_nonneg hCb hCr, ?_⟩
  intro gs hgs_window
  let Fprod : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    section43TimeProductTensor
      (fun i : Fin (d + 1) =>
        section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
  let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
      (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
  have hside_to_boundary :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y Fprod)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝 (TC Fprod)) := by
    simpa [Fprod, TC, F, G, osiiAxisPairPositiveSideCLMC,
      osiiAxisPairPositiveSideCLMR, osiiAxisPairBoundaryCLMC]
      using
        osiiAxisPair_vectorCLMSide_tendsto_boundary_sideCone
          (d := d) OS lgc F G hCside_pos Fprod
  have hgs_boundary :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρb := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρb ρr)
  have hgs_real :
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) →
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρr := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_right ρb ρr)
  have hboundary :
      TC Fprod =
        ∫ τ : Fin (d + 1) → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
            (section43TimeProductSource gs).f τ := by
    simpa [Fprod, TC, F, G] using hboundary_product gs hgs_boundary
  have hbranch_integral :
      (∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
            (section43TimeProductSource gs).f τ) =
        ∫ τ : Fin (d + 1) → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
            (section43TimeProductSource gs).f τ := by
    refine
      integral_mul_eq_of_eqOn_tsupport
        (fun τ : Fin (d + 1) → ℝ =>
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
        ?_
    intro τ hτ
    exact hreal τ (hgs_real τ hτ)
  simpa [hboundary, hbranch_integral] using hside_to_boundary

/-- Lower side-cone product-source branch-integral limit.

The lower raw axis-pair CLM approaches the same boundary CLM through a negative
side cone.  The boundary CLM is then identified with the Schwinger/MZ
time-shell product-source integral by the positive side-cone source-current
theorem.  This is the lower half of the Section 4.3 side-boundary handoff. -/
theorem osiiAxisPair_lowerSide_timeProductTensor_tendsto_branchIntegral_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
              (section43TimeProductTensor
                (fun i : Fin (d + 1) =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ)) := by
  classical
  intro F G
  rcases
    osiiAxisPair_boundaryCLM_productTensor_eq_schwinger_timeShell_lowerSideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      (Cside := Cminus) hCminus_neg with
    ⟨ρb, Cb, hρb, hCb, hboundary_product⟩
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρr, Cr, hρr, hCr, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨min ρb ρr, Cb + Cr, lt_min hρb hρr, add_nonneg hCb hCr, ?_⟩
  intro gs hgs_window
  let Fprod : SchwartzMap (Fin (d + 1) → ℝ) ℂ :=
    section43TimeProductTensor
      (fun i : Fin (d + 1) =>
        section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
  let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
      (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
  have hside_to_boundary :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y Fprod)
        (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
        (𝓝 (TC Fprod)) := by
    simpa [Fprod, TC, F, G, osiiAxisPairLowerSideCLMC,
      osiiAxisPairLowerSideCLMR, osiiAxisPairBoundaryCLMC]
      using
        osiiAxisPair_vectorCLMSide_tendsto_boundary_lowerSideCone
          (d := d) OS lgc F G (Cside := Cminus) hCminus_neg Fprod
  have hgs_boundary :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρb := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρb ρr)
  have hgs_real :
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) →
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρr := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_right ρb ρr)
  have hboundary :
      TC Fprod =
        ∫ τ : Fin (d + 1) → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
            (section43TimeProductSource gs).f τ := by
    simpa [Fprod, TC, F, G] using hboundary_product gs hgs_boundary
  have hbranch_integral :
      (∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
            (section43TimeProductSource gs).f τ) =
        ∫ τ : Fin (d + 1) → ℝ,
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) *
            (section43TimeProductSource gs).f τ := by
    refine
      integral_mul_eq_of_eqOn_tsupport
        (fun τ : Fin (d + 1) → ℝ =>
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        (fun τ : Fin (d + 1) → ℝ =>
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))))
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
        ?_
    intro τ hτ
    exact hreal τ (hgs_real τ hτ)
  simpa [hboundary, hbranch_integral] using hside_to_boundary

/-- Positive side-cone convergence of the actual shifted finite-height
axis-pair branch integrals.

This combines the eventual source-current equality with the boundary
product-source limit: on product generators supported in a smaller time-shell
window, the moving finite-height shifted MZ branch integral tends to the
zero-height branch integral. -/
theorem osiiAxisPair_positiveSide_shiftedBranchProductIntegral_tendsto_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
                (section43TimeProductSource gs).f τ)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ)) := by
  classical
  rcases
    osiiAxisPair_positiveSide_timeProductTensor_tendsto_branchIntegral_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρlim, Clim, hρlim, hClim, hlim⟩
  rcases
    osiiAxisPair_positiveSide_timeProductTensor_eventually_eq_shiftedBranch_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρeq, Ceq, hρeq, hCeq, heq⟩
  refine ⟨min ρlim (ρeq / 2), Clim + Ceq, ?_, add_nonneg hClim hCeq, ?_⟩
  · exact lt_min hρlim (half_pos hρeq)
  intro gs hgs_window
  have hgs_lim :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρlim := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρlim (ρeq / 2))
  have hgs_eq :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρeq / 2) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_right ρlim (ρeq / 2))
  have hraw := hlim gs hgs_lim
  have hevent := heq gs hgs_eq
  have hevent' :
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
            (section43TimeProductSource gs).f τ)
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        osiiAxisPairPositiveSideCLMC (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) y
          (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
    filter_upwards [hevent] with y hy
    exact hy.symm
  exact (tendsto_congr' hevent').2 hraw

/-- Positive-side source cutoff CLMs constructed from one Lemma 5.1 time-shell
packet converge on all supported product sources.

The zero-height and moving finite-height CLMs are constructed from the same
local MZ packet/radius.  This is the concrete source-side transport needed
before the local Section 4.3 closure step, including the pointwise boundedness
needed for the Banach-Steinhaus extension. -/
theorem exists_axisPair_positiveSide_cutoffBranchCLMs_productSource_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ, χ τ = 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χ τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                    φ τ) ∧
          (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆
                osiiAxisPairTimeShellWindow (d := d) ξ ρ →
            Tendsto
              (fun y : Fin (d + 1) → ℝ =>
                Tseq y (section43TimeProductSource gs).f)
              (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
              (𝓝 (T (section43TimeProductSource gs).f))) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ B : ℝ,
            ∀ y : Fin (d + 1) → ℝ, ‖(Tseq y - T) φ‖ ≤ B) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρbranch, Cbranch, hρbranch, hCbranch, hdiff, _hreal, _hselector, hbound⟩
  rcases
    osiiAxisPair_positiveSide_shiftedBranchProductIntegral_tendsto_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos with
    ⟨ρlim, Clim, hρlim, hClim, hlim_products⟩
  let ρ : ℝ := min ρlim (ρbranch / 2)
  refine ⟨ρ, Cbranch + Clim, ?_, add_nonneg hCbranch hClim, ?_⟩
  · exact lt_min hρlim (half_pos hρbranch)
  intro hχ_support hχ_one_window
  have hχ_support_branch :
      tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρbranch := by
    intro τ hτ ν
    have hτ_small := hχ_support hτ ν
    exact lt_of_lt_of_le hτ_small (by
      have hhalf_le : ρbranch / 2 ≤ ρbranch := by linarith
      exact (min_le_right ρlim (ρbranch / 2)).trans hhalf_le)
  let U0 : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρbranch
  let H0 : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have hU0_open : IsOpen U0 := by
    simpa [U0] using
      isOpen_osiiAxisPairTimeShellWindow (d := d) ξ (ρ := ρbranch)
  have hreal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp (continuous_apply ν)
  have hmaps0 :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        U0
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch) := by
    intro τ hτ
    simpa [U0, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hH0_cont : ContinuousOn H0 U0 := by
    simpa [H0, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hreal_cont.continuousOn hmaps0
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      H0 χ hU0_open hχ_compact (by simpa [U0] using hχ_support_branch)
      hH0_cont with
    ⟨T, hT_cut, hT_one⟩
  let shiftedCarrier : (Fin (d + 1) → ℝ) → Prop := fun y =>
    ∀ τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ),
      (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + y 0 else τ ν) ∈
        osiiAxisPairTimeShellWindow (d := d) ξ ρbranch
  have shiftedCLM_exists :
      ∀ y : Fin (d + 1) → ℝ, shiftedCarrier y →
        ∃ L : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            L φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                  φ τ) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            (∀ τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ), χ τ = 1) →
              L φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
                    φ τ := by
    intro y hy_carrier
    let shiftC : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℂ := fun τ ν =>
      ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)
    let Uy : Set (Fin (d + 1) → ℝ) :=
      shiftC ⁻¹' osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch
    let Hy : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ (shiftC τ)
    have hshift_cont : Continuous shiftC := by
      exact continuous_pi fun ν =>
        Fin.cases
          (by
            simp [shiftC]
            fun_prop)
          (fun j => by
            simp [shiftC]
            fun_prop)
          ν
    have hUy_open : IsOpen Uy := by
      exact
        (isOpen_osiiAxisPairTimeShellComplexWindow
          (d := d) ξ (ρ := ρbranch)).preimage hshift_cont
    have hχUy :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆ Uy := by
      intro τ hτ
      have hτ := hy_carrier τ hτ
      simpa [Uy, shiftC, osiiAxisPairTimeShellWindow,
        osiiAxisPairTimeShellComplexWindow,
        osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
    have hmaps_y :
        Set.MapsTo shiftC Uy
          (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch) := by
      intro τ hτ
      exact hτ
    have hHy_cont : ContinuousOn Hy Uy := by
      simpa [Hy, shiftC, osiiAxisPairWeightedTimeShellBranch] using
        hdiff.continuousOn.comp hshift_cont.continuousOn hmaps_y
    rcases
      SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
        Hy χ hUy_open hχ_compact hχUy hHy_cont with
      ⟨L, hL_cut, hL_one⟩
    refine ⟨L, ?_, ?_⟩
    · intro φ
      simpa [Hy, shiftC, mul_assoc] using hL_cut φ
    · intro φ hφ_one
      simpa [Hy, shiftC] using hL_one φ hφ_one
  let Tseq : (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ := fun y =>
    if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy) else 0
  refine ⟨T, Tseq, ?_, ?_, ?_, ?_⟩
  · intro φ
    simpa [H0] using hT_cut φ
  · have hχ_support_half :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hχ_support hτ ν)
        (min_le_right ρlim (ρbranch / 2))
    have hev_carrier :=
      osiiAxisPair_eventually_positive_shifted_tsupport_mem_timeShellWindow
        (d := d) ξ hρbranch χ hχ_support_half hCside_pos
    filter_upwards [hev_carrier] with y hy_carrier φ
    have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
    change
      (if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy)
        else 0) φ =
        ∫ τ : Fin (d + 1) → ℝ,
          (χ τ *
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
            φ τ
    rw [dif_pos hy_carrier]
    exact hspec.1 φ
  · intro gs hgs_window
    have hgs_lim :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρlim := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρlim (ρbranch / 2))
    have hlim := hlim_products gs hgs_lim
    have hχ_one_source :
        ∀ τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ),
          χ τ = 1 := by
      intro τ hτ
      exact hχ_one_window τ (hgs_window hτ)
    have hT_source :
        T (section43TimeProductSource gs).f =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
              (section43TimeProductSource gs).f τ := by
      simpa [H0] using hT_one (section43TimeProductSource gs).f hχ_one_source
    have hχ_support_half :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hχ_support hτ ν)
        (min_le_right ρlim (ρbranch / 2))
    have hev_carrier :=
      osiiAxisPair_eventually_positive_shifted_tsupport_mem_timeShellWindow
        (d := d) ξ hρbranch χ hχ_support_half hCside_pos
    have heq_seq :
        (fun y : Fin (d + 1) → ℝ =>
          Tseq y (section43TimeProductSource gs).f)
          =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
        (fun y : Fin (d + 1) → ℝ =>
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ) := by
      filter_upwards [hev_carrier] with y hy_carrier
      have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
      change
        (if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy)
          else 0) (section43TimeProductSource gs).f =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ
      rw [dif_pos hy_carrier]
      exact hspec.2 (section43TimeProductSource gs).f hχ_one_source
    exact (tendsto_congr' heq_seq).2 (by simpa [hT_source] using hlim)
  · intro φ
    let bound : (Fin (d + 1) → ℝ) → ℝ := fun τ =>
      Cbranch * ‖χ τ * φ τ‖
    have hbound_cont : Continuous bound := by
      exact continuous_const.mul ((χ.continuous.mul φ.continuous).norm)
    have hbound_support_subset :
        Function.support bound ⊆
          Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
      intro τ hτ
      by_contra hχτ_not
      have hχτ : χ τ = 0 := by
        simpa [Function.mem_support] using hχτ_not
      have hbτ : bound τ = 0 := by
        simp [bound, hχτ]
      exact hτ hbτ
    have hbound_tsupport_subset :
        Function.support bound ⊆
          tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) :=
      fun τ hτ => subset_tsupport _ (hbound_support_subset hτ)
    have hbound_compact : HasCompactSupport bound :=
      HasCompactSupport.of_support_subset_isCompact hχ_compact hbound_tsupport_subset
    have hbound_int : Integrable bound volume :=
      hbound_cont.integrable_of_hasCompactSupport hbound_compact
    have hbound_nonneg : ∀ τ : Fin (d + 1) → ℝ, 0 ≤ bound τ := by
      intro τ
      exact mul_nonneg hCbranch (norm_nonneg _)
    have hJ_nonneg : 0 ≤ ∫ τ : Fin (d + 1) → ℝ, bound τ :=
      integral_nonneg hbound_nonneg
    have branch_bound_of_window :
        ∀ τ : Fin (d + 1) → ℝ,
          τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρbranch →
          ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ))‖ ≤ Cbranch := by
      intro τ hτ_window
      have hclosed :
          osiiAxisPairTimeShellPerturbation (d := d) ξ τ ∈
            Metric.closedBall (0 : Fin (d + 1) → ℝ) ρbranch := by
        rw [Metric.mem_closedBall, dist_zero_right,
          pi_norm_le_iff_of_nonneg hρbranch.le]
        intro ν
        have hν := le_of_lt (hτ_window ν)
        simpa [Complex.norm_real, Real.norm_eq_abs] using hν
      simpa [osiiAxisPairWeightedTimeShellBranch,
        osiiAxisPairTimeShellPerturbationC_ofReal] using hbound τ hclosed
    have target_bound : ‖T φ‖ ≤ ∫ τ : Fin (d + 1) → ℝ, bound τ := by
      rw [hT_cut φ]
      refine norm_integral_le_of_norm_le hbound_int ?_
      filter_upwards with τ
      by_cases hχτ : χ τ = 0
      · simp [bound, hχτ]
      · have hτ_support :
            τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) := by
          have hτ_fun :
              τ ∈ Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
            simpa [Function.mem_support] using hχτ
          exact subset_tsupport _ hτ_fun
        have hbranch_bound :=
          branch_bound_of_window τ (hχ_support_branch hτ_support)
        have hχφ_nonneg : 0 ≤ ‖χ τ * φ τ‖ := norm_nonneg _
        calc
          ‖(χ τ *
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ‖
              =
            ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ))‖ *
              ‖χ τ * φ τ‖ := by
                rw [norm_mul, norm_mul, norm_mul]
                ring
          _ ≤ Cbranch * ‖χ τ * φ τ‖ :=
            mul_le_mul_of_nonneg_right hbranch_bound hχφ_nonneg
          _ = bound τ := by
            simp [bound]
    have seq_bound :
        ∀ y : Fin (d + 1) → ℝ, ‖Tseq y φ‖ ≤
          ∫ τ : Fin (d + 1) → ℝ, bound τ := by
      intro y
      by_cases hy_carrier : shiftedCarrier y
      · have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
        rw [show Tseq y = Classical.choose (shiftedCLM_exists y hy_carrier) by
          simp [Tseq, dif_pos hy_carrier]]
        rw [hspec.1 φ]
        refine norm_integral_le_of_norm_le hbound_int ?_
        filter_upwards with τ
        by_cases hχτ : χ τ = 0
        · simp [bound, hχτ]
        · have hτ_support :
              τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) := by
            have hτ_fun :
                τ ∈ Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
              simpa [Function.mem_support] using hχτ
            exact subset_tsupport _ hτ_fun
          have hbranch_bound :=
            branch_bound_of_window
              (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + y 0 else τ ν)
              (hy_carrier τ hτ_support)
          have hχφ_nonneg : 0 ≤ ‖χ τ * φ τ‖ := norm_nonneg _
          calc
            ‖(χ τ *
                osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                φ τ‖
                =
              ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))‖ *
                ‖χ τ * φ τ‖ := by
                  rw [norm_mul, norm_mul, norm_mul]
                  ring
            _ ≤ Cbranch * ‖χ τ * φ τ‖ :=
              mul_le_mul_of_nonneg_right hbranch_bound hχφ_nonneg
            _ = bound τ := by
              simp [bound]
      · have hzero : Tseq y φ = 0 := by
          simp [Tseq, hy_carrier]
        rw [hzero, norm_zero]
        exact hJ_nonneg
    refine ⟨2 * (∫ τ : Fin (d + 1) → ℝ, bound τ), ?_⟩
    intro y
    calc
      ‖(Tseq y - T) φ‖ = ‖Tseq y φ - T φ‖ := by
        rfl
      _ ≤ ‖Tseq y φ‖ + ‖T φ‖ := norm_sub_le _ _
      _ ≤ (∫ τ : Fin (d + 1) → ℝ, bound τ) +
          (∫ τ : Fin (d + 1) → ℝ, bound τ) :=
        add_le_add (seq_bound y) target_bound
      _ = 2 * (∫ τ : Fin (d + 1) → ℝ, bound τ) := by ring

/-- Section 4.3 closure assembly from the concrete positive-side cutoff branch
CLMs.

The product-source packet above supplies both hypotheses of
`section43_tendsto_timeSchwartz_of_axisPairWindow_productCutoff`, so the local
branch convergence extends from compact product sources to any test selected
by the product cutoff. -/
theorem exists_axisPair_positiveSide_cutoffBranchCLMs_timeSchwartz_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
            (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) ∧
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χbranch τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χbranch τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                    φ τ)) := by
  classical
  rcases
    exists_axisPair_positiveSide_cutoffBranchCLMs_productSource_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail F hχ_one
  rcases hpacket hχ_support hχ_one_window with
    ⟨T, Tseq, hT_formula, hTseq_formula, h_on_products, h_pointwise_bounded⟩
  have htend :
      Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) :=
    section43_tendsto_timeSchwartz_of_axisPairWindow_productCutoff
      (d := d) (Tseq := Tseq) (T := T) ξ ρ χs
      hχ_pos hχ_compact hχ_head hχ_tail F hχ_one h_on_products
      h_pointwise_bounded
  exact ⟨T, Tseq, htend, hT_formula, hTseq_formula⟩

/-- Positive side-cone convergence for any compact finite-time test already
carried by the smaller axis-pair window.

This packages the product-cutoff selection step from OS II V.2: from a compact
strict-positive support inside `ρ / 2`, choose coordinatewise one-dimensional
cutoffs supported in the larger `ρ` window, then invoke the product-source
extension theorem. -/
theorem exists_axisPair_positiveSide_cutoffBranchCLMs_timeSchwartz_tendsto_of_compact_support_in_halfWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        HasCompactSupport (F : (Fin (d + 1) → ℝ) → ℂ) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion (d + 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
            (𝓝[Cside] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) ∧
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χbranch τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cside] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χbranch τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + y 0 else τ ν : ℝ) : ℂ))) *
                    φ τ)) := by
  classical
  rcases
    exists_axisPair_positiveSide_cutoffBranchCLMs_timeSchwartz_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCside_pos χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window F hF_compact hF_pos hF_window
  rcases exists_axisPairWindow_productCutoffs_on_compact
      (d := d) ξ hρ hF_compact.isCompact hF_pos hF_window with
    ⟨χs, hχ_pos, hχ_compact, hχ_head, hχ_tail, hχ_one⟩
  exact
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact
      hχ_head hχ_tail F hχ_one

/-- Lower side-cone convergence of the actual shifted finite-height axis-pair
branch integrals. -/
theorem osiiAxisPair_lowerSide_shiftedBranchProductIntegral_tendsto_sideCone
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            ∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
                (section43TimeProductSource gs).f τ)
          (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
          (𝓝
            (∫ τ : Fin (d + 1) → ℝ,
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
                (section43TimeProductSource gs).f τ)) := by
  classical
  rcases
    osiiAxisPair_lowerSide_timeProductTensor_tendsto_branchIntegral_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCminus_neg with
    ⟨ρlim, Clim, hρlim, hClim, hlim⟩
  rcases
    osiiAxisPair_lowerSide_timeProductTensor_eventually_eq_shiftedBranch_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCminus_neg with
    ⟨ρeq, Ceq, hρeq, hCeq, heq⟩
  refine ⟨min ρlim (ρeq / 2), Clim + Ceq, ?_, add_nonneg hClim hCeq, ?_⟩
  · exact lt_min hρlim (half_pos hρeq)
  intro gs hgs_window
  have hgs_lim :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρlim := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρlim (ρeq / 2))
  have hgs_eq :
      tsupport ((section43TimeProductSource gs).f :
        (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρeq / 2) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_right ρlim (ρeq / 2))
  have hraw := hlim gs hgs_lim
  have hevent := heq gs hgs_eq
  have hevent' :
      (fun y : Fin (d + 1) → ℝ =>
        ∫ τ : Fin (d + 1) → ℝ,
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
            (section43TimeProductSource gs).f τ)
        =ᶠ[𝓝[Cminus] (0 : Fin (d + 1) → ℝ)]
      (fun y : Fin (d + 1) → ℝ =>
        osiiAxisPairLowerSideCLMC (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) y
          (section43TimeProductTensor
            (fun i : Fin (d + 1) =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
    filter_upwards [hevent] with y hy
    exact hy.symm
  exact (tendsto_congr' hevent').2 hraw

omit [NeZero d] in
/-- Lower-side collar: if a test support lies in a half-radius time-shell
window, then for sufficiently small negative side height the `-y 0` shifted
support lies in the full window. -/
theorem osiiAxisPair_eventually_lower_shifted_tsupport_mem_timeShellWindow
    (ξ : Fin (d + 1) → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (F : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hF_support :
      tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2))
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    ∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
      ∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
        (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + (-y 0) else τ ν) ∈
          osiiAxisPairTimeShellWindow (d := d) ξ ρ := by
  have hsmall :
      {y : Fin (d + 1) → ℝ | -y 0 < ρ / 2} ∈
        𝓝[Cminus] (0 : Fin (d + 1) → ℝ) := by
    exact mem_nhdsWithin_of_mem_nhds (by
      apply IsOpen.mem_nhds
      · exact isOpen_lt ((continuous_apply 0).neg) continuous_const
      · simpa using (half_pos hρ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hyC hy_small τ hτ
  have hyneg : y 0 < 0 := hCminus_neg hyC
  have hheight : 0 < -y 0 := neg_pos.mpr hyneg
  exact
    osiiAxisPairTimeShellWindow_shift_time_mem
      (d := d) ξ τ hρ (hF_support hτ) (le_of_lt hheight) hy_small

/-- Lower-side source cutoff CLMs constructed from one Lemma 5.1 time-shell
packet converge on all supported product sources. -/
theorem exists_axisPair_lowerSide_cutoffBranchCLMs_productSource_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχ_compact : HasCompactSupport (χ : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ, χ τ = 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χ τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
                    φ τ) ∧
          (∀ gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs).f :
              (Fin (d + 1) → ℝ) → ℂ) ⊆
                osiiAxisPairTimeShellWindow (d := d) ξ ρ →
            Tendsto
              (fun y : Fin (d + 1) → ℝ =>
                Tseq y (section43TimeProductSource gs).f)
              (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
              (𝓝 (T (section43TimeProductSource gs).f))) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ B : ℝ,
            ∀ y : Fin (d + 1) → ℝ, ‖(Tseq y - T) φ‖ ≤ B) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0 with
    ⟨ρbranch, Cbranch, hρbranch, hCbranch, hdiff, _hreal, _hselector, hbound⟩
  rcases
    osiiAxisPair_lowerSide_shiftedBranchProductIntegral_tendsto_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg with
    ⟨ρlim, Clim, hρlim, hClim, hlim_products⟩
  let ρ : ℝ := min ρlim (ρbranch / 2)
  refine ⟨ρ, Cbranch + Clim, ?_, add_nonneg hCbranch hClim, ?_⟩
  · exact lt_min hρlim (half_pos hρbranch)
  intro hχ_support hχ_one_window
  have hχ_support_branch :
      tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
        osiiAxisPairTimeShellWindow (d := d) ξ ρbranch := by
    intro τ hτ ν
    have hτ_small := hχ_support hτ ν
    exact lt_of_lt_of_le hτ_small (by
      have hhalf_le : ρbranch / 2 ≤ ρbranch := by linarith
      exact (min_le_right ρlim (ρbranch / 2)).trans hhalf_le)
  let U0 : Set (Fin (d + 1) → ℝ) :=
    osiiAxisPairTimeShellWindow (d := d) ξ ρbranch
  let H0 : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T0 ξ (fun ν : Fin (d + 1) => (τ ν : ℂ))
  have hU0_open : IsOpen U0 := by
    simpa [U0] using
      isOpen_osiiAxisPairTimeShellWindow (d := d) ξ (ρ := ρbranch)
  have hreal_cont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        (fun ν : Fin (d + 1) => (τ ν : ℂ))) := by
    exact continuous_pi fun ν => Complex.continuous_ofReal.comp (continuous_apply ν)
  have hmaps0 :
      Set.MapsTo
        (fun τ : Fin (d + 1) → ℝ =>
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))
        U0
        (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch) := by
    intro τ hτ
    simpa [U0, osiiAxisPairTimeShellWindow,
      osiiAxisPairTimeShellComplexWindow,
      osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
  have hH0_cont : ContinuousOn H0 U0 := by
    simpa [H0, osiiAxisPairWeightedTimeShellBranch] using
      hdiff.continuousOn.comp hreal_cont.continuousOn hmaps0
  rcases
    SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
      H0 χ hU0_open hχ_compact (by simpa [U0] using hχ_support_branch)
      hH0_cont with
    ⟨T, hT_cut, hT_one⟩
  let shiftedCarrier : (Fin (d + 1) → ℝ) → Prop := fun y =>
    ∀ τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ),
      (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + (-y 0) else τ ν) ∈
        osiiAxisPairTimeShellWindow (d := d) ξ ρbranch
  have shiftedCLM_exists :
      ∀ y : Fin (d + 1) → ℝ, shiftedCarrier y →
        ∃ L : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            L φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χ τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
                  φ τ) ∧
          ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            (∀ τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ), χ τ = 1) →
              L φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) =>
                      ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
                    φ τ := by
    intro y hy_carrier
    let shiftC : (Fin (d + 1) → ℝ) → Fin (d + 1) → ℂ := fun τ ν =>
      ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)
    let Uy : Set (Fin (d + 1) → ℝ) :=
      shiftC ⁻¹' osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch
    let Hy : (Fin (d + 1) → ℝ) → ℂ := fun τ =>
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T0 ξ (shiftC τ)
    have hshift_cont : Continuous shiftC := by
      exact continuous_pi fun ν =>
        Fin.cases
          (by
            simp [shiftC]
            fun_prop)
          (fun j => by
            simp [shiftC]
            fun_prop)
          ν
    have hUy_open : IsOpen Uy := by
      exact
        (isOpen_osiiAxisPairTimeShellComplexWindow
          (d := d) ξ (ρ := ρbranch)).preimage hshift_cont
    have hχUy :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆ Uy := by
      intro τ hτ
      have hτ := hy_carrier τ hτ
      simpa [Uy, shiftC, osiiAxisPairTimeShellWindow,
        osiiAxisPairTimeShellComplexWindow,
        osiiAxisPairTimeShellPerturbationC_ofReal] using hτ
    have hmaps_y :
        Set.MapsTo shiftC Uy
          (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρbranch) := by
      intro τ hτ
      exact hτ
    have hHy_cont : ContinuousOn Hy Uy := by
      simpa [Hy, shiftC, osiiAxisPairWeightedTimeShellBranch] using
        hdiff.continuousOn.comp hshift_cont.continuousOn hmaps_y
    rcases
      SCV.compact_cutoff_integralMultiplierCLM_fin_of_continuousOn
        Hy χ hUy_open hχ_compact hχUy hHy_cont with
      ⟨L, hL_cut, hL_one⟩
    refine ⟨L, ?_, ?_⟩
    · intro φ
      simpa [Hy, shiftC, mul_assoc] using hL_cut φ
    · intro φ hφ_one
      simpa [Hy, shiftC] using hL_one φ hφ_one
  let Tseq : (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ := fun y =>
    if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy) else 0
  refine ⟨T, Tseq, ?_, ?_, ?_, ?_⟩
  · intro φ
    simpa [H0] using hT_cut φ
  · have hχ_support_half :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hχ_support hτ ν)
        (min_le_right ρlim (ρbranch / 2))
    have hev_carrier :=
      osiiAxisPair_eventually_lower_shifted_tsupport_mem_timeShellWindow
        (d := d) ξ hρbranch χ hχ_support_half hCminus_neg
    filter_upwards [hev_carrier] with y hy_carrier φ
    have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
    change
      (if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy)
        else 0) φ =
        ∫ τ : Fin (d + 1) → ℝ,
          (χ τ *
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) =>
                ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
            φ τ
    rw [dif_pos hy_carrier]
    exact hspec.1 φ
  · intro gs hgs_window
    have hgs_lim :
        tsupport ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ) ⊆
            osiiAxisPairTimeShellWindow (d := d) ξ ρlim := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hgs_window hτ ν) (min_le_left ρlim (ρbranch / 2))
    have hlim := hlim_products gs hgs_lim
    have hχ_one_source :
        ∀ τ ∈ tsupport ((section43TimeProductSource gs).f :
            (Fin (d + 1) → ℝ) → ℂ),
          χ τ = 1 := by
      intro τ hτ
      exact hχ_one_window τ (hgs_window hτ)
    have hT_source :
        T (section43TimeProductSource gs).f =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) *
              (section43TimeProductSource gs).f τ := by
      simpa [H0] using hT_one (section43TimeProductSource gs).f hχ_one_source
    have hχ_support_half :
        tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρbranch / 2) := by
      intro τ hτ ν
      exact lt_of_lt_of_le (hχ_support hτ ν)
        (min_le_right ρlim (ρbranch / 2))
    have hev_carrier :=
      osiiAxisPair_eventually_lower_shifted_tsupport_mem_timeShellWindow
        (d := d) ξ hρbranch χ hχ_support_half hCminus_neg
    have heq_seq :
        (fun y : Fin (d + 1) → ℝ =>
          Tseq y (section43TimeProductSource gs).f)
          =ᶠ[𝓝[Cminus] (0 : Fin (d + 1) → ℝ)]
        (fun y : Fin (d + 1) → ℝ =>
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ) := by
      filter_upwards [hev_carrier] with y hy_carrier
      have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
      change
        (if hy : shiftedCarrier y then Classical.choose (shiftedCLM_exists y hy)
          else 0) (section43TimeProductSource gs).f =
          ∫ τ : Fin (d + 1) → ℝ,
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) =>
                  ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ)) *
              (section43TimeProductSource gs).f τ
      rw [dif_pos hy_carrier]
      exact hspec.2 (section43TimeProductSource gs).f hχ_one_source
    exact (tendsto_congr' heq_seq).2 (by simpa [hT_source] using hlim)
  · intro φ
    let bound : (Fin (d + 1) → ℝ) → ℝ := fun τ =>
      Cbranch * ‖χ τ * φ τ‖
    have hbound_cont : Continuous bound := by
      exact continuous_const.mul ((χ.continuous.mul φ.continuous).norm)
    have hbound_support_subset :
        Function.support bound ⊆
          Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
      intro τ hτ
      by_contra hχτ_not
      have hχτ : χ τ = 0 := by
        simpa [Function.mem_support] using hχτ_not
      have hbτ : bound τ = 0 := by
        simp [bound, hχτ]
      exact hτ hbτ
    have hbound_tsupport_subset :
        Function.support bound ⊆
          tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) :=
      fun τ hτ => subset_tsupport _ (hbound_support_subset hτ)
    have hbound_compact : HasCompactSupport bound :=
      HasCompactSupport.of_support_subset_isCompact hχ_compact hbound_tsupport_subset
    have hbound_int : Integrable bound volume :=
      hbound_cont.integrable_of_hasCompactSupport hbound_compact
    have hbound_nonneg : ∀ τ : Fin (d + 1) → ℝ, 0 ≤ bound τ := by
      intro τ
      exact mul_nonneg hCbranch (norm_nonneg _)
    have hJ_nonneg : 0 ≤ ∫ τ : Fin (d + 1) → ℝ, bound τ :=
      integral_nonneg hbound_nonneg
    have branch_bound_of_window :
        ∀ τ : Fin (d + 1) → ℝ,
          τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρbranch →
          ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T0 ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ))‖ ≤ Cbranch := by
      intro τ hτ_window
      have hclosed :
          osiiAxisPairTimeShellPerturbation (d := d) ξ τ ∈
            Metric.closedBall (0 : Fin (d + 1) → ℝ) ρbranch := by
        rw [Metric.mem_closedBall, dist_zero_right,
          pi_norm_le_iff_of_nonneg hρbranch.le]
        intro ν
        have hν := le_of_lt (hτ_window ν)
        simpa [Complex.norm_real, Real.norm_eq_abs] using hν
      simpa [osiiAxisPairWeightedTimeShellBranch,
        osiiAxisPairTimeShellPerturbationC_ofReal] using hbound τ hclosed
    have target_bound : ‖T φ‖ ≤ ∫ τ : Fin (d + 1) → ℝ, bound τ := by
      rw [hT_cut φ]
      refine norm_integral_le_of_norm_le hbound_int ?_
      filter_upwards with τ
      by_cases hχτ : χ τ = 0
      · simp [bound, hχτ]
      · have hτ_support :
            τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) := by
          have hτ_fun :
              τ ∈ Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
            simpa [Function.mem_support] using hχτ
          exact subset_tsupport _ hτ_fun
        have hbranch_bound :=
          branch_bound_of_window τ (hχ_support_branch hτ_support)
        have hχφ_nonneg : 0 ≤ ‖χ τ * φ τ‖ := norm_nonneg _
        calc
          ‖(χ τ *
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ‖
              =
            ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T0 ξ
                (fun ν : Fin (d + 1) => (τ ν : ℂ))‖ *
              ‖χ τ * φ τ‖ := by
                rw [norm_mul, norm_mul, norm_mul]
                ring
          _ ≤ Cbranch * ‖χ τ * φ τ‖ :=
            mul_le_mul_of_nonneg_right hbranch_bound hχφ_nonneg
          _ = bound τ := by
            simp [bound]
    have seq_bound :
        ∀ y : Fin (d + 1) → ℝ, ‖Tseq y φ‖ ≤
          ∫ τ : Fin (d + 1) → ℝ, bound τ := by
      intro y
      by_cases hy_carrier : shiftedCarrier y
      · have hspec := Classical.choose_spec (shiftedCLM_exists y hy_carrier)
        rw [show Tseq y = Classical.choose (shiftedCLM_exists y hy_carrier) by
          simp [Tseq, dif_pos hy_carrier]]
        rw [hspec.1 φ]
        refine norm_integral_le_of_norm_le hbound_int ?_
        filter_upwards with τ
        by_cases hχτ : χ τ = 0
        · simp [bound, hχτ]
        · have hτ_support :
              τ ∈ tsupport (χ : (Fin (d + 1) → ℝ) → ℂ) := by
            have hτ_fun :
                τ ∈ Function.support (χ : (Fin (d + 1) → ℝ) → ℂ) := by
              simpa [Function.mem_support] using hχτ
            exact subset_tsupport _ hτ_fun
          have hbranch_bound :=
            branch_bound_of_window
              (fun ν : Fin (d + 1) => if ν = 0 then τ 0 + (-y 0) else τ ν)
              (hy_carrier τ hτ_support)
          have hχφ_nonneg : 0 ≤ ‖χ τ * φ τ‖ := norm_nonneg _
          calc
            ‖(χ τ *
                osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
                φ τ‖
                =
              ‖osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T0 ξ
                  (fun ν : Fin (d + 1) =>
                    ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))‖ *
                ‖χ τ * φ τ‖ := by
                  rw [norm_mul, norm_mul, norm_mul]
                  ring
            _ ≤ Cbranch * ‖χ τ * φ τ‖ :=
              mul_le_mul_of_nonneg_right hbranch_bound hχφ_nonneg
            _ = bound τ := by
              simp [bound]
      · have hzero : Tseq y φ = 0 := by
          simp [Tseq, hy_carrier]
        rw [hzero, norm_zero]
        exact hJ_nonneg
    refine ⟨2 * (∫ τ : Fin (d + 1) → ℝ, bound τ), ?_⟩
    intro y
    calc
      ‖(Tseq y - T) φ‖ = ‖Tseq y φ - T φ‖ := by
        rfl
      _ ≤ ‖Tseq y φ‖ + ‖T φ‖ := norm_sub_le _ _
      _ ≤ (∫ τ : Fin (d + 1) → ℝ, bound τ) +
          (∫ τ : Fin (d + 1) → ℝ, bound τ) :=
        add_le_add (seq_bound y) target_bound
      _ = 2 * (∫ τ : Fin (d + 1) → ℝ, bound τ) := by ring

/-- Lower-side Section 4.3 closure assembly from the concrete cutoff branch
CLMs. -/
theorem exists_axisPair_lowerSide_cutoffBranchCLMs_timeSchwartz_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ (χs : Fin (d + 1) → SchwartzMap ℝ ℂ),
        (∀ i : Fin (d + 1), tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)) →
        (∀ i : Fin (d + 1), HasCompactSupport ((χs i) : ℝ → ℂ)) →
        (∀ t ∈ tsupport ((χs 0) : ℝ → ℂ),
          ‖((t - ξ 0 / 2 : ℝ) : ℂ)‖ < ρ) →
        (∀ j : Fin d, ∀ t ∈ tsupport ((χs (Fin.succ j)) : ℝ → ℂ),
          ‖((t - ξ (Fin.succ j) : ℝ) : ℂ)‖ < ρ) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        (∀ τ ∈ tsupport (F : (Fin (d + 1) → ℝ) → ℂ),
          section43TimeProductTensor χs τ = 1) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
            (𝓝[Cminus] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) ∧
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χbranch τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χbranch τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
                    φ τ)) := by
  classical
  rcases
    exists_axisPair_lowerSide_cutoffBranchCLMs_productSource_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window χs hχ_pos hχ_compact hχ_head hχ_tail F hχ_one
  rcases hpacket hχ_support hχ_one_window with
    ⟨T, Tseq, hT_formula, hTseq_formula, h_on_products, h_pointwise_bounded⟩
  have htend :
      Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
        (𝓝[Cminus] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) :=
    section43_tendsto_timeSchwartz_of_axisPairWindow_productCutoff
      (d := d) (Tseq := Tseq) (T := T) ξ ρ χs
      hχ_pos hχ_compact hχ_head hχ_tail F hχ_one h_on_products
      h_pointwise_bounded
  exact ⟨T, Tseq, htend, hT_formula, hTseq_formula⟩

/-- Lower side-cone convergence for any compact finite-time test already
carried by the smaller axis-pair window. -/
theorem exists_axisPair_lowerSide_cutoffBranchCLMs_timeSchwartz_tendsto_of_compact_support_in_halfWindow
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T0 : ℝ) (hT0 : 0 < T0)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    (χbranch : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχbranch_compact :
      HasCompactSupport (χbranch : (Fin (d + 1) → ℝ) → ℂ)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (tsupport (χbranch : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        (∀ τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ,
          χbranch τ = 1) →
        ∀ F : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        HasCompactSupport (F : (Fin (d + 1) → ℝ) → ℂ) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion (d + 1) →
        tsupport (F : (Fin (d + 1) → ℝ) → ℂ) ⊆
          osiiAxisPairTimeShellWindow (d := d) ξ (ρ / 2) →
        ∃ T : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
        ∃ Tseq :
            (Fin (d + 1) → ℝ) →
              SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ,
          Tendsto (fun y : Fin (d + 1) → ℝ => Tseq y F)
            (𝓝[Cminus] (0 : Fin (d + 1) → ℝ)) (𝓝 (T F)) ∧
          (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
            T φ =
              ∫ τ : Fin (d + 1) → ℝ,
                (χbranch τ *
                  osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                    f hf_ord g hg_ord T0 ξ
                    (fun ν : Fin (d + 1) => (τ ν : ℂ))) * φ τ) ∧
          (∀ᶠ y in 𝓝[Cminus] (0 : Fin (d + 1) → ℝ),
            ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
              Tseq y φ =
                ∫ τ : Fin (d + 1) → ℝ,
                  (χbranch τ *
                    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                      f hf_ord g hg_ord T0 ξ
                      (fun ν : Fin (d + 1) =>
                        ((if ν = 0 then τ 0 + (-y 0) else τ ν : ℝ) : ℂ))) *
                    φ τ)) := by
  classical
  rcases
    exists_axisPair_lowerSide_cutoffBranchCLMs_timeSchwartz_tendsto
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T0 hT0 ξ hξ0
      hCminus_neg χbranch hχbranch_compact with
    ⟨ρ, C, hρ, hC, hpacket⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro hχ_support hχ_one_window F hF_compact hF_pos hF_window
  rcases exists_axisPairWindow_productCutoffs_on_compact
      (d := d) ξ hρ hF_compact.isCompact hF_pos hF_window with
    ⟨χs, hχ_pos, hχ_compact, hχ_head, hχ_tail, hχ_one⟩
  exact
    hpacket hχ_support hχ_one_window χs hχ_pos hχ_compact
      hχ_head hχ_tail F hχ_one

end OSReconstruction
