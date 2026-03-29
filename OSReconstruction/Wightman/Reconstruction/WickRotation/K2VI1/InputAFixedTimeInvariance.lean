import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAInvariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Transport the existing `xiShift` shell-translation invariance theorem to the
fixed-time center/difference kernel attached to the same witness `G`. This is
the exact shell-level `E1` payoff used on the Input A route. -/
theorem twoPointFixedTimeCenterDiffKernelCLM_translation_invariant_on_differenceShell_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ : SchwartzSpacetime d)
    (a : SpacetimeDim d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N) :
    twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift (SCV.translateSchwartz a χ) h)))) =
      twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) := by
  let Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat 2 d z)
  have hK_meas_xi :
      AEStronglyMeasurable (twoPointXiShiftKernel_local (d := d) Ψ t) volume := by
    simpa [Ψ, twoPointXiShiftKernel_eq_twoPointFixedTimeCenterDiffKernel_local (d := d) G t]
      using hK_meas
  have hK_bound_xi : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointXiShiftKernel_local (d := d) Ψ t x‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
    simpa [Ψ, twoPointXiShiftKernel_eq_twoPointFixedTimeCenterDiffKernel_local (d := d) G t]
      using hK_bound
  simpa [Ψ, twoPointXiShiftKernel_eq_twoPointFixedTimeCenterDiffKernel_local (d := d) G t]
    using
      (twoPointXiShiftKernelCLM_translation_invariant_on_differenceShell_of_positiveSupport_local
        (d := d) (OS := OS) (Ψ := Ψ)
        (hΨ_euclid := by
          intro f
          simpa [Ψ] using hG_euclid f)
        (h := h) hh_pos t ht χ a χ₀ hχ₀ hK_meas_xi C_bd N hC hK_bound_xi)

/-- Specialize the transported shell-translation invariance to the reflected
descended shell used in the Input A fixed-time route. -/
theorem twoPointFixedTimeCenterDiffKernelCLM_translation_invariant_on_reflected_descended_differenceShell_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (a : SpacetimeDim d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local
          (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N) :
    twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift (SCV.translateSchwartz a φ)
                (twoPointCenterShearDescent (d := d) φ
                  (reflectedSchwartzSpacetime (d := d) φ)))))) =
      twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift φ
                (twoPointCenterShearDescent (d := d) φ
                  (reflectedSchwartzSpacetime (d := d) φ)))))) := by
  have hdesc_pos :
      tsupport
          ((twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | 0 < x 0} := by
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) φ hφ_compact hφ_neg
  exact
    twoPointFixedTimeCenterDiffKernelCLM_translation_invariant_on_differenceShell_of_positiveSupport_local
      (d := d) OS G hG_euclid
      (twoPointCenterShearDescent (d := d) φ
        (reflectedSchwartzSpacetime (d := d) φ))
      hdesc_pos t ht φ a χ₀ hχ₀ hK_meas C_bd N hC hK_bound

/-- On a fixed positive-support difference shell, the fixed-time kernel pairing
depends on the center test only through its integral. -/
theorem twoPointFixedTimeCenterDiffKernel_differenceShell_depends_only_on_center_integral_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ₀ u = ∫ u : SpacetimeDim d, χ₁ u)
    (χc : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
      volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N) :
    twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₀ h)))) =
      twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₁ h)))) := by
  let Tfixed : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
      hK_meas C_bd N hC hK_bound
  let E : SchwartzSpacetime d →L[ℂ]
      SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
    (reindexSchwartzFin (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)).comp
      ((flattenSchwartzNPoint (d := d)).comp
        ((twoPointCenterDiffSchwartzCLM (d := d)).comp
          (twoPointDifferenceLiftLeftCLM (d := d) h)))
  let L : SchwartzSpacetime d →L[ℂ] ℂ := Tfixed.comp E
  have hL : IsTranslationInvariantSchwartzCLM L := by
    intro a
    ext χ
    simpa [L, Tfixed, E, ContinuousLinearMap.comp_apply,
      twoPointDifferenceLiftLeftCLM_apply] using
      twoPointFixedTimeCenterDiffKernelCLM_translation_invariant_on_differenceShell_of_positiveSupport_local
        (d := d) (OS := OS) (G := G) hG_euclid
        (h := h) hh_pos t ht χ a χc hχc hK_meas C_bd N hC hK_bound
  obtain ⟨c, hc⟩ := exists_eq_const_integralCLM_of_translationInvariant L hL
  have hχ₀_eval : L χ₀ = c * ∫ u : SpacetimeDim d, χ₀ u := by
    have htmp := congrArg (fun S : SchwartzSpacetime d →L[ℂ] ℂ => S χ₀) hc
    simpa [SchwartzMap.integralCLM_apply, smul_eq_mul] using htmp
  have hχ₁_eval : L χ₁ = c * ∫ u : SpacetimeDim d, χ₁ u := by
    have htmp := congrArg (fun S : SchwartzSpacetime d →L[ℂ] ℂ => S χ₁) hc
    simpa [SchwartzMap.integralCLM_apply, smul_eq_mul] using htmp
  calc
    Tfixed
        (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₀ h)))) = L χ₀ := by
                simp [L, Tfixed, E, twoPointDifferenceLiftLeftCLM_apply]
    _ = c * ∫ u : SpacetimeDim d, χ₀ u := hχ₀_eval
    _ = c * ∫ u : SpacetimeDim d, χ₁ u := by rw [hint]
    _ = L χ₁ := hχ₁_eval.symm
    _ = Tfixed
          (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ₁ h)))) := by
                  simp [L, Tfixed, E, twoPointDifferenceLiftLeftCLM_apply]

end OSReconstruction
