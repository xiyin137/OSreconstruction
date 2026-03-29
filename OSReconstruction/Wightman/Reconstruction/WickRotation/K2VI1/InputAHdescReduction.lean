import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFixedTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAKernelReduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAShiftedRepresentative
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- On the common fixed-time kernel surface, the old Input-A `hdesc` equality is
already formal once the kernel agrees with a shifted real-difference
representative on:

1. the reflected product shell, and
2. the descended difference shell with the same center cutoff.

The center replacement from that same center cutoff to `χ₀` is already paid by
the fixed-time center-value theorem. -/
theorem fixedTimeCenterDiff_hdesc_of_shifted_realDifference_same_center_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ₀ φ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (_hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I)) volume)
    (C_bd : ℝ) (N : ℕ) (_hC : 0 < C_bd)
    (_hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hprod_common :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)))
    (hprod_to_diff_shifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)))
    (hdiff_same_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))) :
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (χ₀ (z 0) *
          (twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
  let hdesc : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) φ
      (reflectedSchwartzSpacetime (d := d) φ)
  have hdesc_pos :
      tsupport ((hdesc : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) φ hφ_compact hφ_neg
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
      (d := d) OS G hG_euclid hdesc hdesc_pos t ht
  have hcommon_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * hdesc (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χ₀ (z 0) * hdesc (z 1)) := by
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (φ (z 0) * hdesc (z 1))
        = c * ∫ u : SpacetimeDim d, φ u := hc φ
      _ = c * ∫ u : SpacetimeDim d, χ₀ u := by rw [hφ_int, hχ₀]
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              (χ₀ (z 0) * hdesc (z 1)) := by
            symm
            exact hc χ₀
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := hprod_common
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * hdesc (z 1)) := by
            simpa [hdesc] using hprod_to_diff_shifted
    _ =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * hdesc (z 1)) := by
            simpa [hdesc] using hdiff_same_center.symm
    _ =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χ₀ (z 0) * hdesc (z 1)) := hcommon_center
    _ =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χ₀ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
            simp [hdesc]

/-- The same-center common-vs-shifted shell equality is not primitive.

If the common fixed-time kernel and the shifted real-difference representative
agree on one fixed normalized-center descended shell, then they already agree
on the descended shell with center cutoff `φ`. The common side uses the fixed-
time center-value theorem, and the shifted representative side uses direct
center factorization. -/
theorem fixedTimeCenterDiff_same_center_of_shifted_realDifference_fixed_center_bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χc φ : SchwartzSpacetime d)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hfixed_common_shifted :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))) :
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (φ (z 0) *
          (twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) =
    ∫ z : NPointDomain d 2,
      k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
        (φ (z 0) *
          (twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
  let hdesc : SchwartzSpacetime d :=
    twoPointCenterShearDescent (d := d) φ
      (reflectedSchwartzSpacetime (d := d) φ)
  have hdesc_pos :
      tsupport ((hdesc : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
        {x : SpacetimeDim d | 0 < x 0} := by
    dsimp [hdesc]
    exact twoPointCenterShearDescent_reflected_tsupport_pos_local
      (d := d) φ hφ_compact hφ_neg
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_fixedTimeCenterDiffKernel_exists_const_local
      (d := d) OS G hG_euclid hdesc hdesc_pos t ht
  have hcommon_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * hdesc (z 1)) =
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc (z 1)) := by
    calc
      ∫ z : NPointDomain d 2,
          twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
            (φ (z 0) * hdesc (z 1))
        = c * ∫ u : SpacetimeDim d, φ u := hc φ
      _ = c * ∫ u : SpacetimeDim d, χc u := by rw [hφ_int, hχc]
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
              (χc (z 0) * hdesc (z 1)) := by
            symm
            exact hc χc
  have hshifted_center :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * hdesc (z 1)) := by
    let Kt : SpacetimeDim d → ℂ :=
      fun ξ => k2DifferenceKernel_real_local (d := d) μ (ξ + timeShiftVec d t)
    calc
      ∫ z : NPointDomain d 2,
          k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
            (χc (z 0) * hdesc (z 1))
        = (∫ u : SpacetimeDim d, χc u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc ξ := by
            exact integral_centerDiff_differenceOnly_kernel_factorizes
              (d := d) Kt χc hdesc
      _ = (∫ u : SpacetimeDim d, φ u) *
            ∫ ξ : SpacetimeDim d, Kt ξ * hdesc ξ := by rw [hχc, hφ_int]
      _ = ∫ z : NPointDomain d 2,
            k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
              (φ (z 0) * hdesc (z 1)) := by
            exact
              (integral_centerDiff_differenceOnly_kernel_factorizes
                (d := d) Kt φ hdesc).symm
  calc
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))
      =
    ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) * hdesc (z 1)) := by
            simpa [hdesc] using hcommon_center
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χc (z 0) * hdesc (z 1)) := by
            simpa [hdesc] using hfixed_common_shifted
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * hdesc (z 1)) := hshifted_center
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
            simp [hdesc]

/-- Even sharper `hdesc` surface: same-center equality is not primitive.

To discharge the common fixed-time `hdesc` step, it is enough to know:

1. common fixed-time kernel = shifted real-difference representative on the
   reflected product shell;
2. the shifted representative already carries reflected product shell to
   same-center descended shell;
3. common fixed-time kernel = shifted representative on one fixed normalized-
   center descended shell.

The same-center common-vs-shifted equality is then formal. -/
theorem fixedTimeCenterDiff_hdesc_of_shifted_realDifference_fixed_center_bridge_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ₀ χc φ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχc : ∫ u : SpacetimeDim d, χc u = 1)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (_hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I)) volume)
    (C_bd : ℝ) (N : ℕ) (_hC : 0 < C_bd)
    (_hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hprod_common :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)))
    (hprod_to_diff_shifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)))
    (hfixed_common_shifted :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χc (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))) :
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (χ₀ (z 0) *
          (twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := by
  have hsame_center :=
    fixedTimeCenterDiff_same_center_of_shifted_realDifference_fixed_center_bridge_local
      (d := d) OS G hG_euclid χc φ hχc hφ_int hφ_compact hφ_neg t ht μ
      hfixed_common_shifted
  exact
    fixedTimeCenterDiff_hdesc_of_shifted_realDifference_same_center_bridges_local
      (d := d) OS G hG_euclid χ₀ φ hχ₀ hφ_int hφ_compact hφ_neg t ht
      (by
        simpa using _hK_meas)
      C_bd N _hC
      (by
        simpa using _hK_bound)
      μ hprod_common hprod_to_diff_shifted hsame_center

/-- CLM-level form of the same-center shifted-real-difference bridge. Once the
two shell equalities against the explicit shifted representative are known, the
current Input-A `hdesc` equality is already formal. -/
theorem fixedTimeCenterDiff_hdesc_clm_of_shifted_realDifference_same_center_bridges_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ₀ φ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hφ_int : ∫ u : SpacetimeDim d, φ u = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (t : ℝ) (ht : 0 < t)
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (hprod_common :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)))
    (hprod_to_diff_shifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)))
    (hdiff_same_center :
      ∫ z : NPointDomain d 2,
        twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (φ (z 0) *
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) (z 1))) :
    let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
      twoPointFlatKernelCLM
        (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
        hK_meas C_bd N hC hK_bound
    T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift φ
                (reflectedSchwartzSpacetime (d := d) φ))))) =
      T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₀
                (twoPointCenterShearDescent (d := d) φ
                  (reflectedSchwartzSpacetime (d := d) φ)))))) := by
  let T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM
      (twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I))
      hK_meas C_bd N hC hK_bound
  have hbridge :=
    fixedTimeCenterDiff_hdesc_of_shifted_realDifference_same_center_bridges_local
      (d := d) OS G hG_euclid χ₀ φ hχ₀ hφ_int hφ_compact hφ_neg t ht
      hK_meas C_bd N hC hK_bound μ hprod_common hprod_to_diff_shifted hdiff_same_center
  calc
    T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift φ
                (reflectedSchwartzSpacetime (d := d) φ)))))
      =
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (φ (z 0) * reflectedSchwartzSpacetime (d := d) φ (z 0 + z 1)) := by
          simpa [T, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointProductLift_apply] using
            (OSReconstruction.twoPointFlatKernelCLM_apply_reindex_flatten
              (d := d)
              (K := OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                (d := d) G ((t : ℂ) * Complex.I))
              hK_meas C_bd N hC hK_bound
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift φ
                  (reflectedSchwartzSpacetime (d := d) φ))))
    _ =
    ∫ z : NPointDomain d 2,
      twoPointFixedTimeCenterDiffKernel_local (d := d) G ((t : ℂ) * Complex.I) z *
        (χ₀ (z 0) *
          (OSReconstruction.twoPointCenterShearDescent (d := d) φ
            (reflectedSchwartzSpacetime (d := d) φ)) (z 1)) := hbridge
    _ =
    T (reindexSchwartzFin
          (show 2 * (d + 1) = (d + 1) + (d + 1) by ring)
          (flattenSchwartzNPoint (d := d)
            (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ₀
                (OSReconstruction.twoPointCenterShearDescent (d := d) φ
                  (reflectedSchwartzSpacetime (d := d) φ)))))) := by
          symm
          simpa [T, OSReconstruction.twoPointCenterDiffSchwartzCLM_twoPointDifferenceLift] using
            (OSReconstruction.twoPointFlatKernelCLM_apply_reindex_flatten
              (d := d)
              (K := OSReconstruction.twoPointFixedTimeCenterDiffKernel_local
                (d := d) G ((t : ℂ) * Complex.I))
              hK_meas C_bd N hC hK_bound
              (OSReconstruction.twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ₀
                  (OSReconstruction.twoPointCenterShearDescent (d := d) φ
                    (reflectedSchwartzSpacetime (d := d) φ)))))

/-- Honest packaging of the remaining shifted-representative shell route.

To discharge the current Input-A `hdesc` equality, it is enough to know:

1. the common fixed-time kernel agrees with the shifted real-difference
   representative on the reflected product shell;
2. the shifted representative turns that reflected product shell into the
   canonical descended difference shell with the same center cutoff;
3. the common fixed-time kernel agrees with the shifted representative on the
   descended shell with the target center cutoff.

The rest is formal. -/
theorem fixedTimeCenterDiff_productShell_to_difference_of_shifted_realDifference_bridge_local
    (K : NPointDomain d 2 → ℂ)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (χ χ₀ g : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ u = ∫ u : SpacetimeDim d, χ₀ u)
    (hprod_common :
      ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * g (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)))
    (hprod_to_diff_shifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)))
    (hdiff_bridge :
      ∫ z : NPointDomain d 2,
        K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1))) :
    ∫ z : NPointDomain d 2,
      K z * (χ (z 0) * g (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
  calc
    ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * g (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)) := hprod_common
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := hprod_to_diff_shifted
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
            exact OSReconstruction.shifted_realDifferenceKernel_differenceShell_depends_only_on_center_integral_local
              (d := d) μ χ χ₀ (twoPointCenterShearDescent (d := d) χ g) hint t
    _ =
    ∫ z : NPointDomain d 2,
        K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := hdiff_bridge.symm

/-- Sharper bridge when the common kernel side already has its own descended
shell center-replacement theorem. Then the shifted representative only needs to
match the common kernel on the reflected product shell and on the descended
shell with the same center cutoff. -/
theorem fixedTimeCenterDiff_productShell_to_difference_of_shifted_realDifference_via_common_shell_invariance_local
    (K : NPointDomain d 2 → ℂ)
    (μ : Measure (ℝ × (Fin d → ℝ)))
    (t : ℝ)
    (χ χ₀ g : SchwartzSpacetime d)
    (hprod_common :
      ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * g (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)))
    (hprod_to_diff_shifted :
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)))
    (hdiff_same_center :
      ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) =
      ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)))
    (hcommon_center :
      ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) =
      ∫ z : NPointDomain d 2,
        K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1))) :
    ∫ z : NPointDomain d 2,
      K z * (χ (z 0) * g (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := by
  calc
    ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * g (z 0 + z 1))
      =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * g (z 0 + z 1)) := hprod_common
    _ =
    ∫ z : NPointDomain d 2,
        k2DifferenceKernel_real_local (d := d) μ (z 1 + timeShiftVec d t) *
          (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := hprod_to_diff_shifted
    _ =
    ∫ z : NPointDomain d 2,
        K z * (χ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := hdiff_same_center.symm
    _ =
    ∫ z : NPointDomain d 2,
        K z * (χ₀ (z 0) * (twoPointCenterShearDescent (d := d) χ g) (z 1)) := hcommon_center

end OSReconstruction
