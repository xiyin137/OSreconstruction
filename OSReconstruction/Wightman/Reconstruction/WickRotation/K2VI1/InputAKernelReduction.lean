import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Integrate a two-point center/difference kernel in the center variable
against a fixed Schwartz cutoff. -/
def centerIntegratedTwoPointKernel_local
    (K : NPointDomain d 2 → ℂ)
    (χ : SchwartzSpacetime d) : SpacetimeDim d → ℂ :=
  fun ξ => ∫ u : SpacetimeDim d, K (Fin.cons u (fun _ => ξ)) * χ u

theorem continuous_centerIntegratedTwoPointKernel_local
    (K : NPointDomain d 2 → ℂ)
    (hK_cont : Continuous K)
    (χ : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ)) :
    Continuous (centerIntegratedTwoPointKernel_local (d := d) K χ) := by
  let F : SpacetimeDim d → SpacetimeDim d → ℂ :=
    fun ξ u => K (Fin.cons u (fun _ => ξ)) * χ u
  have hmap_cont :
      Continuous (fun p : SpacetimeDim d × SpacetimeDim d =>
        Fin.cons p.2 (fun _ => p.1)
          : SpacetimeDim d × SpacetimeDim d → NPointDomain d 2) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa using continuous_snd
    · simpa using continuous_fst
  have hF_cont : Continuous F.uncurry := by
    have hK' :
        Continuous (fun p : SpacetimeDim d × SpacetimeDim d =>
          K (Fin.cons p.2 (fun _ => p.1))) :=
      hK_cont.comp hmap_cont
    have hχ' : Continuous (fun p : SpacetimeDim d × SpacetimeDim d => χ p.2) := by
      exact (SchwartzMap.continuous χ).comp continuous_snd
    simpa [F, Function.uncurry] using hK'.mul hχ'
  have hk : IsCompact (tsupport (χ : SpacetimeDim d → ℂ)) := by
    simpa using hχ_compact
  have hF_zero :
      ∀ p u, p ∈ (Set.univ : Set (SpacetimeDim d)) →
        u ∉ tsupport (χ : SpacetimeDim d → ℂ) → F p u = 0 := by
    intro p u _ hu
    have hu0 : χ u = 0 := image_eq_zero_of_notMem_tsupport hu
    simp [F, hu0]
  have hcont :
      ContinuousOn (fun ξ => ∫ u, F ξ u ∂volume) (Set.univ : Set (SpacetimeDim d)) := by
    simpa using
      (continuousOn_integral_of_compact_support
        (μ := volume) (s := (Set.univ : Set (SpacetimeDim d)))
        (k := tsupport (χ : SpacetimeDim d → ℂ))
        hk hF_cont.continuousOn hF_zero)
  rw [← continuousOn_univ]
  simpa [centerIntegratedTwoPointKernel_local, F] using hcont

theorem integral_centerIntegratedTwoPointKernel_factorizes_local
    (K : NPointDomain d 2 → ℂ)
    (hK_cont : Continuous K)
    (χ : SchwartzSpacetime d)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) =
      ∫ ξ : SpacetimeDim d,
        centerIntegratedTwoPointKernel_local (d := d) K χ ξ * h ξ := by
  let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
    MeasurableEquiv.finTwoArrow
  have heprod :
      MeasureTheory.MeasurePreserving eprod
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [eprod] using
      (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
  let F : SpacetimeDim d → SpacetimeDim d → ℂ :=
    fun u ξ => K (Fin.cons u (fun _ => ξ)) * (χ u * h ξ)
  have hmap_cont :
      Continuous (fun p : SpacetimeDim d × SpacetimeDim d =>
        Fin.cons p.1 (fun _ => p.2)
          : SpacetimeDim d × SpacetimeDim d → NPointDomain d 2) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa using continuous_fst
    · simpa using continuous_snd
  have hF_cont : Continuous F.uncurry := by
    have hK' :
        Continuous (fun p : SpacetimeDim d × SpacetimeDim d =>
          K (Fin.cons p.1 (fun _ => p.2))) :=
      hK_cont.comp hmap_cont
    have hχ' : Continuous (fun p : SpacetimeDim d × SpacetimeDim d => χ p.1) := by
      exact (SchwartzMap.continuous χ).comp continuous_fst
    have hh' : Continuous (fun p : SpacetimeDim d × SpacetimeDim d => h p.2) := by
      exact (SchwartzMap.continuous h).comp continuous_snd
    simpa [F, Function.uncurry, mul_assoc] using hK'.mul (hχ'.mul hh')
  have hF_compact : HasCompactSupport F.uncurry := by
    refine HasCompactSupport.intro
      (K := (tsupport (χ : SpacetimeDim d → ℂ)) ×ˢ (tsupport (h : SpacetimeDim d → ℂ))) ?_ ?_
    · simpa using (show IsCompact ((tsupport (χ : SpacetimeDim d → ℂ)) ×ˢ
        (tsupport (h : SpacetimeDim d → ℂ))) from hχ_compact.prod hh_compact)
    · intro p hp
      have hp' : p.1 ∉ tsupport (χ : SpacetimeDim d → ℂ) ∨ p.2 ∉ tsupport (h : SpacetimeDim d → ℂ) := by
        by_cases hp1 : p.1 ∈ tsupport (χ : SpacetimeDim d → ℂ)
        · right
          intro hp2
          exact hp ⟨hp1, hp2⟩
        · exact Or.inl hp1
      rcases hp' with hp1 | hp2
      · have hp10 : χ p.1 = 0 := image_eq_zero_of_notMem_tsupport hp1
        simp [Function.uncurry, F, hp10]
      · have hp20 : h p.2 = 0 := image_eq_zero_of_notMem_tsupport hp2
        simp [Function.uncurry, F, hp20]
  have hF_int : Integrable F.uncurry (volume.prod volume) := by
    exact hF_cont.integrable_of_hasCompactSupport hF_compact
  have hcomp :
      ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1)) =
        ∫ p : SpacetimeDim d × SpacetimeDim d,
          K (Fin.cons p.1 (Fin.cons p.2 finZeroElim)) * (χ p.1 * h p.2) := by
    simpa [eprod, MeasurableEquiv.finTwoArrow, mul_assoc] using
      (heprod.symm.integral_comp'
        (g := fun z : NPointDomain d 2 => K z * (χ (z 0) * h (z 1)))).symm
  have hcomp_F :
      ∫ p : SpacetimeDim d × SpacetimeDim d,
        K (Fin.cons p.1 (Fin.cons p.2 finZeroElim)) * (χ p.1 * h p.2)
        = ∫ p : SpacetimeDim d × SpacetimeDim d, F p.1 p.2 := by
    refine integral_congr_ae ?_
    filter_upwards with p
    have hFin :
        (Fin.cons p.1 (Fin.cons p.2 finZeroElim) : NPointDomain d 2) =
          Fin.cons p.1 (fun _ => p.2) := by
      ext i
      fin_cases i <;> rfl
    simp [F, hFin]
  calc
    ∫ z : NPointDomain d 2, K z * (χ (z 0) * h (z 1))
      = ∫ p : SpacetimeDim d × SpacetimeDim d, F p.1 p.2 := hcomp.trans hcomp_F
    _ = ∫ u : SpacetimeDim d, ∫ ξ : SpacetimeDim d, F u ξ := by
          symm
          simpa using MeasureTheory.integral_integral hF_int
    _ = ∫ ξ : SpacetimeDim d, ∫ u : SpacetimeDim d, F u ξ := by
          simpa using MeasureTheory.integral_integral_swap hF_int
    _ = ∫ ξ : SpacetimeDim d,
          centerIntegratedTwoPointKernel_local (d := d) K χ ξ * h ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          dsimp [centerIntegratedTwoPointKernel_local, F]
          calc
            ∫ u : SpacetimeDim d, K (Fin.cons u (fun _ => ξ)) * (χ u * h ξ)
                = ∫ u : SpacetimeDim d, (K (Fin.cons u (fun _ => ξ)) * χ u) * h ξ := by
                    refine integral_congr_ae ?_
                    filter_upwards with u
                    ring
            _ = (∫ u : SpacetimeDim d, K (Fin.cons u (fun _ => ξ)) * χ u) * h ξ := by
                    exact MeasureTheory.integral_mul_const _ _

theorem exists_common_difference_kernel_of_common_center_kernel_pairing_local
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχ₀_compact : HasCompactSupport (χ₀ : SpacetimeDim d → ℂ))
    (K₂ : NPointDomain d 2 → ℂ)
    (hK₂_cont : Continuous K₂)
    (χ_seq : ℕ → SchwartzSpacetime d)
    (hχ_seq_compact : ∀ n, HasCompactSupport (χ_seq n : SpacetimeDim d → ℂ))
    (I : ℕ → ℂ)
    (hpair : ∀ n,
      I n = ∫ z : NPointDomain d 2, K₂ z * (χ₀ (z 0) * χ_seq n (z 1))) :
    ∃ K_s : SpacetimeDim d → ℂ,
      Continuous K_s ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K_s x *
              twoPointDifferenceLift χ₀ (χ_seq n) x := by
  refine ⟨centerIntegratedTwoPointKernel_local (d := d) K₂ χ₀, ?_, ?_⟩
  · exact continuous_centerIntegratedTwoPointKernel_local
      (d := d) K₂ hK₂_cont χ₀ hχ₀_compact
  · intro n
    calc
      I n = ∫ z : NPointDomain d 2, K₂ z * (χ₀ (z 0) * χ_seq n (z 1)) := hpair n
      _ = ∫ ξ : SpacetimeDim d,
            centerIntegratedTwoPointKernel_local (d := d) K₂ χ₀ ξ * χ_seq n ξ := by
            exact integral_centerIntegratedTwoPointKernel_factorizes_local
              (d := d) K₂ hK₂_cont χ₀ hχ₀_compact (χ_seq n) (hχ_seq_compact n)
      _ = (∫ u : SpacetimeDim d, χ₀ u) *
            ∫ ξ : SpacetimeDim d,
              centerIntegratedTwoPointKernel_local (d := d) K₂ χ₀ ξ * χ_seq n ξ := by
            simp [hχ₀]
      _ = ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel
                (d := d) (centerIntegratedTwoPointKernel_local (d := d) K₂ χ₀) x *
              twoPointDifferenceLift χ₀ (χ_seq n) x := by
            symm
            exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
              (d := d)
              (centerIntegratedTwoPointKernel_local (d := d) K₂ χ₀)
              χ₀ (χ_seq n)

theorem exists_common_difference_kernel_of_aux_compact_center_pairing_local
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hχc_compact : HasCompactSupport (χc : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K₂ : NPointDomain d 2 → ℂ)
    (hK₂_cont : Continuous K₂)
    (χ_seq : ℕ → SchwartzSpacetime d)
    (hχ_seq_compact : ∀ n, HasCompactSupport (χ_seq n : SpacetimeDim d → ℂ))
    (I : ℕ → ℂ)
    (hpair : ∀ n,
      I n = ∫ z : NPointDomain d 2, K₂ z * (χc (z 0) * χ_seq n (z 1))) :
    ∃ K_s : SpacetimeDim d → ℂ,
      Continuous K_s ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K_s x *
              twoPointDifferenceLift χ₀ (χ_seq n) x := by
  obtain ⟨K_s, hK_s_cont, hpairc⟩ :=
    exists_common_difference_kernel_of_common_center_kernel_pairing_local
      (d := d) χc hχc hχc_compact K₂ hK₂_cont χ_seq hχ_seq_compact I hpair
  refine ⟨K_s, hK_s_cont, ?_⟩
  intro n
  calc
    I n = ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χc (χ_seq n) x := hpairc n
    _ = (∫ u : SpacetimeDim d, χc u) *
          ∫ ξ : SpacetimeDim d, K_s ξ * χ_seq n ξ := by
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K_s χc (χ_seq n)
    _ = ∫ ξ : SpacetimeDim d, K_s ξ * χ_seq n ξ := by
          simp [hχc]
    _ = (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d, K_s ξ * χ_seq n ξ := by
          simp [hχ₀]
    _ = ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ (χ_seq n) x := by
          symm
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K_s χ₀ (χ_seq n)

/-- A head-block-translation-invariant flattened two-point functional sees two
difference lifts with the same center integral as equal. -/
theorem map_twoPointDifferenceLift_eq_of_centerIntegral_eq_of_headBlockTranslationInvariant_local
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := d + 1) (n := d + 1) T)
    (χ₀ χ₁ h : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ₀ u = ∫ u : SpacetimeDim d, χ₁ u) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₀ h)))) =
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₁ h)))) := by
  let F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d)
          (twoPointDifferenceLift χ₀ h)))
  let G : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    reindexSchwartzFin (by ring)
      (flattenSchwartzNPoint (d := d)
        (twoPointCenterDiffSchwartzCLM (d := d)
          (twoPointDifferenceLift χ₁ h)))
  apply map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant
    (m := d + 1) (n := d + 1) T hT F G
  have hdesc₀ :
      twoPointCenterDescent (d := d) (twoPointDifferenceLift χ₀ h) =
        (∫ u : SpacetimeDim d, χ₀ u) • h :=
    twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul (d := d) χ₀ h
  have hdesc₁ :
      twoPointCenterDescent (d := d) (twoPointDifferenceLift χ₁ h) =
        (∫ u : SpacetimeDim d, χ₁ u) • h :=
    twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul (d := d) χ₁ h
  calc
    integrateHeadBlock (m := d + 1) (n := d + 1) F
      = (∫ u : SpacetimeDim d, χ₀ u) • h := by
          simpa [F, twoPointCenterDescent] using hdesc₀
    _ = (∫ u : SpacetimeDim d, χ₁ u) • h := by rw [hint]
    _ = integrateHeadBlock (m := d + 1) (n := d + 1) G := by
          simpa [G, twoPointCenterDescent] using hdesc₁.symm

/-- A common product-shell pairing already yields the common descended
difference-kernel pairing needed for Input A, once the underlying flattened
kernel functional is head-block translation invariant. -/
theorem exists_common_difference_kernel_of_common_productShell_pairing_headBlockInvariant_local
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hχc_compact : HasCompactSupport (χc : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K₂ : NPointDomain d 2 → ℂ)
    (hK₂_cont : Continuous K₂)
    (hK_meas : AEStronglyMeasurable K₂ volume)
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K₂ x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hTinv : IsHeadBlockTranslationInvariantSchwartzCLM (m := d + 1) (n := d + 1)
      (twoPointFlatKernelCLM (d := d) K₂ hK_meas C_bd N hC hK_bound))
    (φ_seq g_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ u : SpacetimeDim d, φ_seq n u = 1)
    (hdesc_compact : ∀ n,
      HasCompactSupport ((twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (I : ℕ → ℂ)
    (hpair : ∀ n,
      I n = ∫ z : NPointDomain d 2, K₂ z * (φ_seq n (z 0) * g_seq n (z 0 + z 1))) :
    ∃ K_s : SpacetimeDim d → ℂ,
      Continuous K_s ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K_s x *
              twoPointDifferenceLift χ₀
                (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) x := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM (d := d) K₂ hK_meas C_bd N hC hK_bound
  have hpair' : ∀ n,
      I n =
        ∫ z : NPointDomain d 2,
          K₂ z *
            (χc (z 0) * (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) (z 1)) := by
    intro n
    have hprod :
        I n =
          T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n) (g_seq n))))) := by
      calc
        I n = ∫ z : NPointDomain d 2, K₂ z * (φ_seq n (z 0) * g_seq n (z 0 + z 1)) := hpair n
        _ = T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift (φ_seq n) (g_seq n))))) := by
              symm
              simpa [T, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
                (twoPointFlatKernelCLM_apply_reindex_flatten
                  (d := d) (K := K₂) hK_meas C_bd N hC hK_bound
                  (twoPointCenterDiffSchwartzCLM (d := d)
                    (twoPointProductLift (φ_seq n) (g_seq n))))
    have hdesc :
        T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift (φ_seq n) (g_seq n))))) =
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift (φ_seq n)
                    (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := by
      simpa [twoPointCenterShearDescent_eq,
        twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift_eq_productTensor] using
        (map_twoPointProductShell_eq_canonicalDifferenceLift_of_headBlockTranslationInvariant
          (d := d) T hTinv (φ_seq n) (hφ_int n) (g_seq n))
    have hcenter :
        T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift (φ_seq n)
                    (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) =
          T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χc
                    (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := by
      exact map_twoPointDifferenceLift_eq_of_centerIntegral_eq_of_headBlockTranslationInvariant_local
        (d := d) T hTinv (φ_seq n) χc
        (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n))
        (by rw [hφ_int n, hχc])
    calc
      I n = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n) (g_seq n))))) := hprod
      _ = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := hdesc
      _ = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χc
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := hcenter
      _ = ∫ z : NPointDomain d 2,
            K₂ z *
              (χc (z 0) * (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) (z 1)) := by
            simpa [T, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
              (twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K₂) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χc
                    (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))
  exact exists_common_difference_kernel_of_aux_compact_center_pairing_local
    (d := d) χc hχc hχc_compact χ₀ hχ₀ K₂ hK₂_cont
    (fun n => twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n))
    hdesc_compact I hpair'

/-- More honest Input A reduction: it is enough to know the concrete family-level
product-shell to canonical-difference-shell equality for the common flattened
kernel functional, rather than a global head-block invariance package. -/
theorem exists_common_difference_kernel_of_common_productShell_pairing_local
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hχc_compact : HasCompactSupport (χc : SpacetimeDim d → ℂ))
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (K₂ : NPointDomain d 2 → ℂ)
    (hK₂_cont : Continuous K₂)
    (hK_meas : AEStronglyMeasurable K₂ volume)
    (C_bd : ℝ)
    (N : ℕ)
    (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖K₂ x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (φ_seq g_seq : ℕ → SchwartzSpacetime d)
    (hφ_int : ∀ n, ∫ u : SpacetimeDim d, φ_seq n u = 1)
    (hdesc_compact : ∀ n,
      HasCompactSupport ((twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (hdesc : ∀ n,
      let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
        twoPointFlatKernelCLM (d := d) K₂ hK_meas C_bd N hC hK_bound
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n) (g_seq n))))) =
        T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))))
    (hcenter : ∀ n,
      let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
        twoPointFlatKernelCLM (d := d) K₂ hK_meas C_bd N hC hK_bound
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) =
        T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χc
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))))
    (I : ℕ → ℂ)
    (hpair : ∀ n,
      I n = ∫ z : NPointDomain d 2, K₂ z * (φ_seq n (z 0) * g_seq n (z 0 + z 1))) :
    ∃ K_s : SpacetimeDim d → ℂ,
      Continuous K_s ∧
      ∀ n,
        I n =
          ∫ x : NPointDomain d 2,
            twoPointDifferenceKernel (d := d) K_s x *
              twoPointDifferenceLift χ₀
                (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) x := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM (d := d) K₂ hK_meas C_bd N hC hK_bound
  have hpair' : ∀ n,
      I n =
        ∫ z : NPointDomain d 2,
          K₂ z *
            (χc (z 0) * (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) (z 1)) := by
    intro n
    have hprod :
        I n =
          T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n) (g_seq n))))) := by
      calc
        I n = ∫ z : NPointDomain d 2, K₂ z * (φ_seq n (z 0) * g_seq n (z 0 + z 1)) := hpair n
        _ = T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointProductLift (φ_seq n) (g_seq n))))) := by
              symm
              simpa [T, twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
                (twoPointFlatKernelCLM_apply_reindex_flatten
                  (d := d) (K := K₂) hK_meas C_bd N hC hK_bound
                  (twoPointCenterDiffSchwartzCLM (d := d)
                    (twoPointProductLift (φ_seq n) (g_seq n))))
    calc
      I n = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift (φ_seq n) (g_seq n))))) := hprod
      _ = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift (φ_seq n)
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := by
            simpa [T] using hdesc n
      _ = T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χc
                  (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))) := by
            simpa [T] using hcenter n
      _ = ∫ z : NPointDomain d 2,
            K₂ z *
              (χc (z 0) * (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)) (z 1)) := by
            simpa [T, twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
              (twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := K₂) hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χc
                    (twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n)))))
  exact exists_common_difference_kernel_of_aux_compact_center_pairing_local
    (d := d) χc hχc hχc_compact χ₀ hχ₀ K₂ hK₂_cont
    (fun n => twoPointCenterShearDescent (d := d) (φ_seq n) (g_seq n))
    hdesc_compact I hpair'

end OSReconstruction
