import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIINarrowTimeStageChart

/-!
# Centered logarithmic growth for ordered-product packets

The raw narrow-time logarithmic coordinate contains the common shift
`-log (2 d T)`. Bounding packet translations before removing that shift
produces a spurious slope-dependent coefficient. This file records the
normalized estimate in centered logarithmic coordinates, where the `T` in
the axis-pair directions cancels the `1 / T` coefficient scale.
-/

noncomputable section

open Set
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Real logarithmic coordinates recentered by the common narrow-time scale. -/
def osiiNarrowTimeCenteredRealLogCoordinate
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    Fin k → osiiAxisPairIndex d → ℝ :=
  fun i a => x i a + Real.log (osiiNarrowTimeLogScale (d := d) T)

/-- For slope at least one, every axis-pair direction has product norm at
most the slope itself. -/
theorem norm_osiiAxisPairDir_le_slope
    (T : ℝ) (hT : 1 ≤ T)
    (a : osiiAxisPairIndex d) :
    ‖osiiAxisPairDir (d := d) T a‖ ≤ T := by
  rcases a with ⟨a, b⟩
  rw [pi_norm_le_iff_of_nonneg (le_trans (by norm_num) hT)]
  intro μ
  refine Fin.cases ?_ ?_ μ
  · change |T| ≤ T
    rw [abs_of_nonneg (le_trans (by norm_num) hT)]
  · intro j
    by_cases haj : a = j
    · subst j
      cases b <;> simp [osiiAxisPairDir, hT]
    · simp only [osiiAxisPairDir, Fin.cases_succ, if_neg haj, norm_zero]
      exact le_trans (by norm_num) hT

/-- One raw logarithmic coefficient times its physical direction is bounded
by the exponential of the centered coordinate. This is the basic
`T * (1 / T)` cancellation. -/
theorem exp_mul_norm_osiiAxisPairDir_le_exp_centered
    (T : ℝ) (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    Real.exp (x i a) * ‖osiiAxisPairDir (d := d) T a‖ ≤
      Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a) := by
  let scale := osiiNarrowTimeLogScale (d := d) T
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hscale : 0 < scale :=
    osiiNarrowTimeLogScale_pos (d := d) T hT0
  have hd : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdir :
      ‖osiiAxisPairDir (d := d) T a‖ ≤ T :=
    norm_osiiAxisPairDir_le_slope T hT.le a
  have hTscale : T ≤ scale := by
    dsimp [scale, osiiNarrowTimeLogScale]
    nlinarith
  calc
    Real.exp (x i a) * ‖osiiAxisPairDir (d := d) T a‖
        ≤ Real.exp (x i a) * scale :=
      mul_le_mul_of_nonneg_left
        (hdir.trans hTscale) (Real.exp_pos _).le
    _ = Real.exp (x i a + Real.log scale) := by
      rw [Real.exp_add, Real.exp_log hscale]
    _ =
        Real.exp
          (osiiNarrowTimeCenteredRealLogCoordinate T x i a) := by
      rfl

/-- The full chronological translation majorant is bounded by the sum of
centered coefficient exponentials, with no slope-dependent multiplier. -/
theorem osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_sum
    (T : ℝ) (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairChronologicalTranslationMajorant T x ≤
      ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a) := by
  apply Finset.sum_le_sum
  intro i _hi
  apply Finset.sum_le_sum
  intro a _ha
  exact exp_mul_norm_osiiAxisPairDir_le_exp_centered T hT x i a

/-- Number of chronological logarithmic coordinates, viewed as a real
coefficient for the centered cosh estimate. -/
def osiiAxisPairCenteredTranslationCoshConstant : ℝ :=
  ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d, 1

theorem osiiAxisPairCenteredTranslationCoshConstant_nonneg :
    0 ≤ osiiAxisPairCenteredTranslationCoshConstant (d := d) (k := k) := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by norm_num

/-- The chronological translation majorant has a centered cosh-growth bound
whose multiplicative coefficient is independent of the slope. -/
theorem osiiAxisPairChronologicalTranslationMajorant_le_centered_cosh
    (T : ℝ) (hT : 1 < T)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    osiiAxisPairChronologicalTranslationMajorant T x ≤
      osiiAxisPairCenteredTranslationCoshConstant (d := d) (k := k) *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiNarrowTimeCenteredRealLogCoordinate T x))) := by
  let E :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten
            (osiiNarrowTimeCenteredRealLogCoordinate T x)))
  have hcoord :
      ∀ i : Fin k, ∀ a : osiiAxisPairIndex d,
        Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a) ≤ E := by
    intro i a
    simpa [E] using
      (SCV.exp_coord_le_exp_four_mul_logCoshGauge
        (osiiAxisPairMultiGapFlatten
          (osiiNarrowTimeCenteredRealLogCoordinate T x))
        (osiiAxisPairMultiGapFlattenIndex (i, a)))
  calc
    osiiAxisPairChronologicalTranslationMajorant T x
        ≤ ∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp (osiiNarrowTimeCenteredRealLogCoordinate T x i a) :=
      osiiAxisPairChronologicalTranslationMajorant_le_centered_exp_sum
        T hT x
    _ ≤ ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d, E := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro a _ha
      exact hcoord i a
    _ =
        osiiAxisPairCenteredTranslationCoshConstant
            (d := d) (k := k) * E := by
      simp [osiiAxisPairCenteredTranslationCoshConstant]
      ring
    _ =
        osiiAxisPairCenteredTranslationCoshConstant
            (d := d) (k := k) *
          Real.exp
            (4 *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiNarrowTimeCenteredRealLogCoordinate T x))) := by
      rfl

/-- Slope-free affine coefficient for packet configurations once the actual
center-offset vector is bounded by `B`. -/
def OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
    (B : ℝ) : ℝ :=
  1 +
    2 * osiiAxisPairCenteredTranslationCoshConstant (d := d) (k := k) +
    B

theorem
    OSIIChronologicalCompactFactors.one_add_norm_packetLeftConfiguration_le_centered_cosh
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (B : ℝ) (hB : 0 ≤ B)
    (hcenter :
      ‖F.packetCenterOffsetVector T hordered q‖ ≤ B) :
    1 + ‖F.packetLeftConfiguration T hordered x q‖ ≤
      OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
          (d := d) (k := k) B *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiNarrowTimeCenteredRealLogCoordinate T x))) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K :=
    osiiAxisPairCenteredTranslationCoshConstant (d := d) (k := k)
  let E :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten
            (osiiNarrowTimeCenteredRealLogCoordinate T x)))
  have hconfig :
      ‖F.packetLeftConfiguration T hordered x q‖ ≤ 2 * M + B := by
    calc
      ‖F.packetLeftConfiguration T hordered x q‖
          ≤ 2 * M + ‖F.packetCenterOffsetVector T hordered q‖ := by
        simpa [M] using
          F.norm_packetLeftConfiguration_le_majorant
            T hordered x q
      _ ≤ 2 * M + B := by linarith
  have hM : M ≤ K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_centered_cosh
        (d := d) (k := k) T hT x
  have hK : 0 ≤ K := by
    exact osiiAxisPairCenteredTranslationCoshConstant_nonneg
      (d := d) (k := k)
  have hE : 1 ≤ E := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le))
  dsimp
    [OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant]
  change 1 + ‖F.packetLeftConfiguration T hordered x q‖ ≤
    (1 + 2 * K + B) * E
  nlinarith

theorem
    OSIIChronologicalCompactFactors.one_add_norm_packetRightConfiguration_le_centered_cosh
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k)
    (B : ℝ) (hB : 0 ≤ B)
    (hcenter :
      ‖F.packetCenterOffsetVector T hordered q‖ ≤ B) :
    1 + ‖F.packetRightConfiguration T hordered x q‖ ≤
      OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
          (d := d) (k := k) B *
        Real.exp
          (4 *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiNarrowTimeCenteredRealLogCoordinate T x))) := by
  let M := osiiAxisPairChronologicalTranslationMajorant T x
  let K :=
    osiiAxisPairCenteredTranslationCoshConstant (d := d) (k := k)
  let E :=
    Real.exp
      (4 *
        SCV.logCoshGauge
          (osiiAxisPairMultiGapFlatten
            (osiiNarrowTimeCenteredRealLogCoordinate T x)))
  have hconfig :
      ‖F.packetRightConfiguration T hordered x q‖ ≤ 2 * M + B := by
    calc
      ‖F.packetRightConfiguration T hordered x q‖
          ≤ 2 * M + ‖F.packetCenterOffsetVector T hordered q‖ := by
        simpa [M] using
          F.norm_packetRightConfiguration_le_majorant
            T hordered x q
      _ ≤ 2 * M + B := by linarith
  have hM : M ≤ K * E := by
    simpa [M, K, E] using
      osiiAxisPairChronologicalTranslationMajorant_le_centered_cosh
        (d := d) (k := k) T hT x
  have hK : 0 ≤ K := by
    exact osiiAxisPairCenteredTranslationCoshConstant_nonneg
      (d := d) (k := k)
  have hE : 1 ≤ E := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le))
  dsimp
    [OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant]
  change 1 + ‖F.packetRightConfiguration T hordered x q‖ ≤
    (1 + 2 * K + B) * E
  nlinarith

end OSReconstruction
