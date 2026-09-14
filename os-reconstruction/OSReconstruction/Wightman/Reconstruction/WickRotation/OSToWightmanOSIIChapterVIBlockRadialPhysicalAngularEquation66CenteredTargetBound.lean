import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66QuantitativeGeometry

/-!
# OS II Chapter VI: polynomial equation-(6.6) target bound

After centering the logarithmic coordinates, exponentiation multiplies each
physical target coefficient by the normalization `2 * d * T`.  The
quantitative first-carrier scale cancels that slope exactly.  Consequently
the complete centered target contributes only a dimension/arity constant
times the physical center norm to the compactified MZ estimate.
-/

noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

theorem osiiEquation66AngleAperture_lt_one
    (d k : Nat) [NeZero d] [NeZero k] :
    osiiEquation66AngleAperture d k < 1 := by
  let c : Real := (k * Fintype.card (osiiAxisPairIndex d) : Nat)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have ha : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
  have hc1Nat : 1 <= k * Fintype.card (osiiAxisPairIndex d) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hk ha))
  have hc1 : 1 <= c := by
    dsimp [c]
    exact_mod_cast hc1Nat
  have hx0 : 0 <= Real.pi / (16 * c) := by positivity
  have hxlt : Real.pi / (16 * c) < Real.pi / 4 := by
    have hden : (4 : Real) < 16 * c := by nlinarith
    exact (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by positivity)).mpr hden
  calc
    osiiEquation66AngleAperture d k =
        Real.tan (Real.pi / (16 * c)) := by
      simp [osiiEquation66AngleAperture, c]
    _ < Real.tan (Real.pi / 4) :=
      Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0
        (by nlinarith [Real.pi_pos]) hxlt
    _ = 1 := Real.tan_pi_div_four

theorem osiiEquation66FirstCarrier_coordinate_scaled_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (y : Fin (k * (d + 1)) -> Real)
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4))
    (p : Fin (k * (d + 1))) :
    (d : Real) * T * |y p| <= rho := by
  let eta := osiiEquation66AngleAperture d k
  let sigma := osiiEquation66FirstCarrierScale d k rho T
  have heta0 : 0 < eta := osiiEquation66AngleAperture_pos d k
  have heta1 : eta < 1 := osiiEquation66AngleAperture_lt_one d k
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hT0 : 0 < T := lt_trans (by norm_num) hT
  have hdT : 0 < (d : Real) * T := mul_pos hd hT0
  have hynorm : norm y <= sigma / 4 := by
    simpa [sigma, Metric.mem_closedBall, dist_zero_right] using hy
  have hcoord : |y p| <= norm y := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y p
  have hsigma : sigma <= eta * rho / (8 * (d : Real) * T) :=
    osiiEquation66FirstCarrierScale_le_angle d k rho T
  have hraw :
      |y p| <= eta * rho / (32 * ((d : Real) * T)) := by
    calc
      |y p| <= norm y := hcoord
      _ <= sigma / 4 := hynorm
      _ <= (eta * rho / (8 * (d : Real) * T)) / 4 :=
        div_le_div_of_nonneg_right hsigma (by norm_num)
      _ = eta * rho / (32 * ((d : Real) * T)) := by ring
  calc
    (d : Real) * T * |y p| <=
        (d : Real) * T *
          (eta * rho / (32 * ((d : Real) * T))) :=
      mul_le_mul_of_nonneg_left hraw hdT.le
    _ = eta * rho / 32 := by
      field_simp [hd.ne', hT0.ne']
    _ <= rho := by nlinarith

theorem osiiEquation66FirstCarrier_coordinate_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (y : Fin (k * (d + 1)) -> Real)
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4))
    (p : Fin (k * (d + 1))) :
    |y p| <= rho := by
  have hd_one : 1 <= (d : Real) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdT_one : 1 <= (d : Real) * T := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= (d : Real) * T :=
        mul_le_mul hd_one hT.le (by norm_num) (by norm_num)
  have hy0 : 0 <= |y p| := abs_nonneg _
  calc
    |y p| = 1 * |y p| := by ring
    _ <= ((d : Real) * T) * |y p| :=
      mul_le_mul_of_nonneg_right hdT_one hy0
    _ <= rho :=
      osiiEquation66FirstCarrier_coordinate_scaled_le
        d k hrho hT y hy p

theorem osiiStep4MultiGapTargetCoeff_scaled_norm_le_three_mul_norm
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4))
    (i : Fin k) (a : osiiAxisPairIndex d) :
    osiiNarrowTimeLogScale (d := d) T *
        norm (osiiStep4MultiGapTargetCoeff d k T center y i a) <=
      3 * norm center := by
  rcases a with ⟨j, b⟩
  let ct := center (finProdFinEquiv (i, (0 : Fin (d + 1))))
  let yt := y (finProdFinEquiv (i, (0 : Fin (d + 1))))
  let ys := y (finProdFinEquiv (i, Fin.succ j))
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hT0 : 0 < T := lt_trans (by norm_num) hT
  have hdT : 0 < (d : Real) * T := mul_pos hd hT0
  have hscale : 0 < osiiNarrowTimeLogScale (d := d) T :=
    osiiNarrowTimeLogScale_pos T hT0
  have hct : 0 < ct := by
    exact hrho.trans_le (hcenter i)
  have hctnorm : ct <= norm center := by
    have := norm_le_pi_norm center
      (finProdFinEquiv (i, (0 : Fin (d + 1))))
    simpa [ct, Real.norm_eq_abs, abs_of_pos hct] using this
  have hrhonorm : rho <= norm center := (hcenter i).trans hctnorm
  have hyt : |yt| <= rho := by
    exact osiiEquation66FirstCarrier_coordinate_le
      d k hrho hT y hy (finProdFinEquiv (i, (0 : Fin (d + 1))))
  have hys : (d : Real) * T * |ys| <= rho := by
    exact osiiEquation66FirstCarrier_coordinate_scaled_le
      d k hrho hT y hy (finProdFinEquiv (i, Fin.succ j))
  have hre :
      (osiiStep4MultiGapTargetCoeff d k T center y i (j, b)).re =
        ct / (4 * (d : Real) * T) := by
    cases b <;>
      simp [osiiStep4MultiGapTargetCoeff, osiiStep4MultiGapRealBlock,
        osiiStep4MultiGapImaginaryBlock, osiiStep4ComplexOfRealImag,
        osiiAxisPairCoeffMap, osiiAxisPairCoeff, ct, Complex.div_re] <;>
      field_simp [hd.ne', hT0.ne']
  have him_eq :
      (osiiStep4MultiGapTargetCoeff d k T center y i (j, b)).im =
        yt / (2 * (d : Real) * T) +
          (if b then ys / 2 else -ys / 2) := by
    cases b <;>
      simp [osiiStep4MultiGapTargetCoeff, osiiStep4MultiGapRealBlock,
        osiiStep4MultiGapImaginaryBlock, osiiStep4ComplexOfRealImag,
        osiiAxisPairCoeffMap, osiiAxisPairCoeff, yt, ys,
        Complex.div_im] <;>
      field_simp [hd.ne', hT0.ne']
  have him :
      |(osiiStep4MultiGapTargetCoeff d k T center y i (j, b)).im| <=
        |yt| / (2 * (d : Real) * T) + |ys| / 2 := by
    rw [him_eq]
    calc
      |yt / (2 * (d : Real) * T) +
          (if b then ys / 2 else -ys / 2)| <=
        |yt / (2 * (d : Real) * T)| +
          |if b then ys / 2 else -ys / 2| := abs_add_le _ _
      _ = |yt| / (2 * (d : Real) * T) + |ys| / 2 := by
        rw [abs_div, abs_of_pos
          (show 0 < 2 * (d : Real) * T by positivity)]
        cases b <;> simp [abs_div]
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (osiiStep4MultiGapTargetCoeff d k T center y i (j, b))
  calc
    osiiNarrowTimeLogScale (d := d) T *
        norm (osiiStep4MultiGapTargetCoeff d k T center y i (j, b)) <=
      osiiNarrowTimeLogScale (d := d) T *
        (|(osiiStep4MultiGapTargetCoeff d k T center y i (j, b)).re| +
          |(osiiStep4MultiGapTargetCoeff d k T center y i (j, b)).im|) :=
      mul_le_mul_of_nonneg_left hnorm hscale.le
    _ <= osiiNarrowTimeLogScale (d := d) T *
        (ct / (4 * (d : Real) * T) +
          (|yt| / (2 * (d : Real) * T) + |ys| / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hscale.le
      rw [hre, abs_of_pos (div_pos hct (by positivity))]
      exact add_le_add (le_refl _) him
    _ = ct / 2 + |yt| + (d : Real) * T * |ys| := by
      simp only [osiiNarrowTimeLogScale]
      field_simp [hd.ne', hT0.ne']
      ring
    _ <= norm center / 2 + rho + rho := by gcongr
    _ <= 3 * norm center := by
      nlinarith [norm_nonneg center]

theorem exp_osiiStep4MultiGapTargetCenteredInput_eq_scale_mul_norm
    (d k : Nat) [NeZero d] [NeZero k]
    (T : Real) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin k) (a : osiiAxisPairIndex d) :
    Real.exp
        (osiiStep4MultiGapTargetCenteredInput d k
          (Real.log (osiiNarrowTimeLogScale (d := d) T))
          T center y i a) =
      osiiNarrowTimeLogScale (d := d) T *
        norm (osiiStep4MultiGapTargetCoeff d k T center y i a) := by
  have hT0 : 0 < T := lt_trans (by norm_num) hT
  have hscale : 0 < osiiNarrowTimeLogScale (d := d) T :=
    osiiNarrowTimeLogScale_pos T hT0
  have hexp := osiiStep4MultiGapTargetLog_exp
    d k T hT0 center y hcenter i a
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp] at hnorm
  simp only [osiiStep4MultiGapTargetCenteredInput, Real.exp_add]
  rw [Real.exp_log hscale, hnorm]
  ring

theorem osiiStep4MultiGapTargetCenteredInput_exp_sum_le
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
      Real.exp
        (osiiStep4MultiGapTargetCenteredInput d k
          (Real.log (osiiNarrowTimeLogScale (d := d) T))
          T center y i a)) <=
      ((k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) * 3) *
        norm center := by
  have hcenter0 : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
    intro i
    exact hrho.trans_le (hcenter i)
  calc
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        Real.exp
          (osiiStep4MultiGapTargetCenteredInput d k
            (Real.log (osiiNarrowTimeLogScale (d := d) T))
            T center y i a)) <=
      ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d,
        3 * norm center := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro a _ha
      rw [exp_osiiStep4MultiGapTargetCenteredInput_eq_scale_mul_norm
        d k T hT center y hcenter0 i a]
      exact osiiStep4MultiGapTargetCoeff_scaled_norm_le_three_mul_norm
        d k hrho hT center y hcenter hy i a
    _ = ((k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) * 3) *
        norm center := by
      simp
      ring

/-- Dimension/arity-only loss in the centered physical target bound. -/
def osiiEquation66CenteredTargetGrowthFactor
    (d k : Nat) [NeZero d] [NeZero k] : Real :=
  1 + Real.exp osiiEquation66UniversalStripParameters.radius *
    ((k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) * 3)

theorem osiiEquation66CenteredTargetGrowthFactor_pos
    (d k : Nat) [NeZero d] [NeZero k] :
    0 < osiiEquation66CenteredTargetGrowthFactor d k := by
  unfold osiiEquation66CenteredTargetGrowthFactor
  positivity

theorem osiiStep4MultiGapTargetCenteredInput_polynomial_bound
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    1 + norm center +
        Real.exp osiiEquation66UniversalStripParameters.radius *
          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp
              (osiiStep4MultiGapTargetCenteredInput d k
                (Real.log (osiiNarrowTimeLogScale (d := d) T))
                T center y i a)) <=
      osiiEquation66CenteredTargetGrowthFactor d k *
        (1 + norm center) := by
  let q : Real :=
    (k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) * 3
  have hq : 0 <= q := by
    dsimp [q]
    positivity
  have hsum := osiiStep4MultiGapTargetCenteredInput_exp_sum_le
    d k hrho hT center y hcenter hy
  have hExp : 0 < Real.exp osiiEquation66UniversalStripParameters.radius :=
    Real.exp_pos _
  calc
    1 + norm center +
        Real.exp osiiEquation66UniversalStripParameters.radius *
          (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
            Real.exp
              (osiiStep4MultiGapTargetCenteredInput d k
                (Real.log (osiiNarrowTimeLogScale (d := d) T))
                T center y i a)) <=
      1 + norm center +
        Real.exp osiiEquation66UniversalStripParameters.radius *
          (q * norm center) := by
        gcongr
    _ = 1 +
        (1 + Real.exp osiiEquation66UniversalStripParameters.radius * q) *
          norm center := by ring
    _ <= (1 + Real.exp osiiEquation66UniversalStripParameters.radius * q) *
        (1 + norm center) := by
      nlinarith [norm_nonneg center]
    _ = osiiEquation66CenteredTargetGrowthFactor d k *
        (1 + norm center) := by
      rfl

end OSReconstruction
