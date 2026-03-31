import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCClosure

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Reduced final-assembly bridge: to recover the full origin-avoiding shell
agreement for the sectorwise common kernel, it is enough to know the compactly
supported reduced pairing only for one fixed center cutoff `χ₀`.

The key point is that the left-hand side already defines a continuous linear
functional on `zeroOriginAvoidingSubmodule d`, so compact-support equality on
that reduced domain extends by density to all reduced tests. The existing
zero-origin pairing theorem for `commonDifferenceKernel_real_local` then turns
that reduced equality into the full two-point shell identity. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCompactFixedCenter_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hK_meas : AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (hShell₀ :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))))
    (χ h : SchwartzSpacetime d)
    (h0 : (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ)) :
    ∫ x : NPointDomain d 2,
      commonK2TimeParametricKernel_real_local (d := d) G x *
        twoPointDifferenceLift χ h x =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  let L₁ : zeroOriginAvoidingSubmodule d →L[ℂ] ℂ :=
    (OSReconstruction.twoPointZeroDiagonalKernelCLM
      (d := d)
      (commonK2TimeParametricKernel_real_local (d := d) G)
      hK_meas C_bd N hC hK_bound).comp
        (twoPointDifferenceLiftFixedCenterZeroDiagCLM χ₀)
  let L₂ : zeroOriginAvoidingSubmodule d →L[ℂ] ℂ :=
    OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
      (d := d) OS χ₀
  have hEq_compact :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
          L₁ h = L₂ h := by
    intro h hh_compact
    simpa [L₁, L₂, ContinuousLinearMap.comp_apply,
      twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical]
      using hShell₀ h hh_compact
  have hEq :
      L₁ = L₂ := by
    exact ContinuousLinearMap.eq_of_eq_on_zeroOriginAvoiding_compactSupport
      (d := d) L₁ L₂ hEq_compact
  have hReduced :
      ∀ h : zeroOriginAvoidingSubmodule d,
        ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) =
          (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
            (d := d) OS χ₀) h := by
    intro h
    have hEq_apply :
        L₁ h = L₂ h := by
      exact congrArg (fun L : zeroOriginAvoidingSubmodule d →L[ℂ] ℂ => L h) hEq
    have hL₁ :
        L₁ h =
          ∫ ξ : SpacetimeDim d,
            commonDifferenceKernel_real_local (d := d) G ξ *
              ((h : SchwartzSpacetime d) ξ) := by
      have hv :
          VanishesToInfiniteOrderOnCoincidence
            (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) := by
        exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
          (h : SchwartzSpacetime d) h.property
      calc
        L₁ h =
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
            simp [L₁]
        _ =
          ∫ x : NPointDomain d 2,
            commonK2TimeParametricKernel_real_local (d := d) G x *
              (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x) := by
            rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply]
            rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
              (f := twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) hv]
        _ =
          (∫ u : SpacetimeDim d, χ₀ u) *
            ∫ ξ : SpacetimeDim d,
              commonDifferenceKernel_real_local (d := d) G ξ *
                ((h : SchwartzSpacetime d) ξ) := by
            simpa [commonK2TimeParametricKernel_real_local] using
              (integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
                (d := d)
                (commonDifferenceKernel_real_local (d := d) G)
                χ₀ (h : SchwartzSpacetime d))
        _ =
          ∫ ξ : SpacetimeDim d,
            commonDifferenceKernel_real_local (d := d) G ξ *
              ((h : SchwartzSpacetime d) ξ) := by
            rw [hχ₀, one_mul]
    calc
      ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) = L₁ h := by
              symm
              exact hL₁
      _ = L₂ h := hEq_apply
      _ =
        (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
          (d := d) OS χ₀) h := by
            rfl
  exact
    commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCLM_pairing_local
      (d := d) OS χ₀ hχ₀ G hReduced χ h h0

/-- The compact fixed-center shell theorem is independent of the chosen
normalized center cutoff.

Once the common sectorwise kernel matches `OS.S 2` on compact reduced shells for
one normalized cutoff `χ₀`, the same statement automatically holds for every
other normalized cutoff `χ₁`, because both the kernel side and the Schwinger
side already depend on the center test only through its integral. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCompactFixedCenter_change_cutoff_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχ₁ : ∫ u : SpacetimeDim d, χ₁ u = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hK_meas : AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (hShell₀ :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))))
    (h : zeroOriginAvoidingSubmodule d)
    (hh_compact : HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
      SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₁ (h : SchwartzSpacetime d))) =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₁ (h : SchwartzSpacetime d))) := by
  have hReduced :
      ∫ ξ : SpacetimeDim d,
        commonDifferenceKernel_real_local (d := d) G ξ *
          ((h : SchwartzSpacetime d) ξ) =
      (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
        (d := d) OS χ₀) h := by
    calc
      ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) =
        (∫ u : SpacetimeDim d, χ₀ u) *
          ∫ ξ : SpacetimeDim d,
            commonDifferenceKernel_real_local (d := d) G ξ *
              ((h : SchwartzSpacetime d) ξ) := by
              rw [hχ₀, one_mul]
      _ =
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
              symm
              exact twoPointZeroDiagonalKernelCLM_commonK2TimeParametricKernel_real_eq_centerValue_local
                (d := d) G hK_meas C_bd N hC hK_bound χ₀ h
      _ =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
              exact hShell₀ h hh_compact
      _ =
        (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
          (d := d) OS χ₀) h := by
              rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_apply]
  calc
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₁ (h : SchwartzSpacetime d))) =
      (∫ u : SpacetimeDim d, χ₁ u) *
        ∫ ξ : SpacetimeDim d,
          commonDifferenceKernel_real_local (d := d) G ξ *
            ((h : SchwartzSpacetime d) ξ) := by
              exact twoPointZeroDiagonalKernelCLM_commonK2TimeParametricKernel_real_eq_centerValue_local
                (d := d) G hK_meas C_bd N hC hK_bound χ₁ h
    _ =
      ∫ ξ : SpacetimeDim d,
        commonDifferenceKernel_real_local (d := d) G ξ *
          ((h : SchwartzSpacetime d) ξ) := by
            rw [hχ₁, one_mul]
    _ =
      (OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
        (d := d) OS χ₀) h := hReduced
    _ =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₁ (h : SchwartzSpacetime d))) := by
            symm
            rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
              (d := d) (OS := OS) χ₀ hχ₀ χ₁ h]
            rw [hχ₁, mul_one]

/-- Flat-origin assembly now reduces to compact origin-avoiding shell equality
for the fixed center cutoff `χ₀`.

This packages the two remaining formal steps:
1. compact fixed-center equality extends to all reduced origin-avoiding tests;
2. compact origin-avoiding shell agreement upgrades to all classical
   flat-origin difference shells by the public closure bridge. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_flatOrigin_differenceShell_of_zeroOriginCompactFixedCenter_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hK_meas : AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (hShell₀ :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))))
    (χ h : SchwartzSpacetime d) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  refine differenceShell_agreement_of_zeroOriginAvoidingCompact_local
    (d := d) OS
    (commonK2TimeParametricKernel_real_local (d := d) G)
    hK_meas C_bd N hC hK_bound ?_ χ h
  intro χ' h' h0 hcompact
  have hv :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointDifferenceLift χ' h') := by
    exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ' h' h0
  calc
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ' h')) =
      ∫ x : NPointDomain d 2,
        commonK2TimeParametricKernel_real_local (d := d) G x *
          (twoPointDifferenceLift χ' h' x) := by
            rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply]
            rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
              (f := twoPointDifferenceLift χ' h') hv]
    _ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ' h')) := by
        exact
          commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCompactFixedCenter_local
            (d := d) OS χ₀ hχ₀ G hK_meas C_bd N hC hK_bound hShell₀ χ' h' h0

end OSReconstruction
