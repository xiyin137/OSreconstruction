/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTargetIdentification











noncomputable section

open Complex Metric Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

namespace SCV.StripCompactificationParameters

/-- Reuse one strip compactification after decreasing the target budget and
increasing the available image width. -/
def weaken
    {S S0 sigma0 sigma : Real}
    (P : SCV.StripCompactificationParameters S0 sigma0)
    (hS : S <= S0)
    (hsigma : sigma0 <= sigma) :
    SCV.StripCompactificationParameters S sigma where
  slope := P.slope
  radius := P.radius
  slope_pos := P.slope_pos
  radius_pos := P.radius_pos
  two_mul_slope_lt_radius := P.two_mul_slope_lt_radius
  inverse_budget := by
    exact (div_le_div_of_nonneg_right hS P.slope_pos.le).trans_lt
      P.inverse_budget
  tangent_budget := P.tangent_budget.trans_le hsigma

end SCV.StripCompactificationParameters

/-- A dimension/arity-only sector aperture with a fixed global argument
margin. -/
def osiiEquation66AngleAperture
    (d k : Nat) [NeZero d] [NeZero k] : Real :=
  Real.tan (Real.pi /
    (16 * ((k * Fintype.card (osiiAxisPairIndex d) : Nat) : Real)))

theorem osiiEquation66AngleAperture_pos
    (d k : Nat) [NeZero d] [NeZero k] :
    0 < osiiEquation66AngleAperture d k := by
  let c : Real := (k * Fintype.card (osiiAxisPairIndex d) : Nat)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have ha : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Nat.mul_pos hk ha
  have hx : 0 < Real.pi / (16 * c) := by positivity
  have hxlt : Real.pi / (16 * c) < Real.pi / 2 := by
    have hc1Nat :
        1 <= k * Fintype.card (osiiAxisPairIndex d) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hk ha))
    have hc1 : 1 <= c := by
      dsimp [c]
      exact_mod_cast hc1Nat
    have hden : (2 : Real) < 16 * c := by nlinarith
    exact (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by positivity)).mpr hden
  exact Real.tan_pos_of_pos_of_lt_pi_div_two hx hxlt

theorem osiiEquation66AngleAperture_budget
    (d k : Nat) [NeZero d] [NeZero k] :
    (k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) *
        Real.arctan (osiiEquation66AngleAperture d k) <
      Real.pi / 8 := by
  let c : Real := (k * Fintype.card (osiiAxisPairIndex d) : Nat)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have ha : 0 < Fintype.card (osiiAxisPairIndex d) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Nat.mul_pos hk ha
  let x : Real := Real.pi / (16 * c)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxlt : x < Real.pi / 2 := by
    dsimp [x]
    have hc1Nat :
        1 <= k * Fintype.card (osiiAxisPairIndex d) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hk ha))
    have hc1 : 1 <= c := by
      dsimp [c]
      exact_mod_cast hc1Nat
    have hden : (2 : Real) < 16 * c := by nlinarith
    exact (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by positivity)).mpr hden
  have hxlow : -(Real.pi / 2) < x := by nlinarith [Real.pi_pos, hx]
  have harctan :
      Real.arctan (osiiEquation66AngleAperture d k) = x := by
    simpa [osiiEquation66AngleAperture, x, c] using
      (Real.arctan_tan hxlow hxlt)
  rw [harctan]
  have hcast :
      (k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) = c := by
    dsimp [c]
    norm_num
  rw [hcast]
  dsimp [x]
  field_simp [hc.ne']
  nlinarith [Real.pi_pos]

/-- The scale on which the complete equation-(6.6) target has a fixed
argument margin.  Its only variable geometric loss is the common slope. -/
def osiiEquation66FirstCarrierScale
    (d k : Nat) [NeZero d] [NeZero k]
    (rho T : Real) : Real :=
  min (rho / 2)
    (osiiEquation66AngleAperture d k * rho /
      (8 * (d : Real) * T))

theorem osiiEquation66FirstCarrierScale_pos
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 0 < T) :
    0 < osiiEquation66FirstCarrierScale d k rho T := by
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  apply lt_min
  · positivity
  · exact div_pos
      (mul_pos (osiiEquation66AngleAperture_pos d k) hrho)
      (mul_pos (mul_pos (by norm_num) hd) hT)

theorem osiiEquation66FirstCarrierScale_le_half
    (d k : Nat) [NeZero d] [NeZero k]
    (rho T : Real) :
    osiiEquation66FirstCarrierScale d k rho T <= rho / 2 :=
  min_le_left _ _

theorem osiiEquation66FirstCarrierScale_le_angle
    (d k : Nat) [NeZero d] [NeZero k]
    (rho T : Real) :
    osiiEquation66FirstCarrierScale d k rho T <=
      osiiEquation66AngleAperture d k * rho /
        (8 * (d : Real) * T) :=
  min_le_right _ _

/-- On the quantitative scale, every block of physical target coefficients
lies in one dimension/arity-only narrow sector. -/
theorem osiiStep4MultiGapTargetCoeff_mem_equation66_narrowSector
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    forall i : Fin k,
      osiiStep4MultiGapTargetCoeff d k T center y i ∈
        osiiAxisPairNarrowSector
          (d := d) (osiiEquation66AngleAperture d k) := by
  let eta := osiiEquation66AngleAperture d k
  let sigma := osiiEquation66FirstCarrierScale d k rho T
  have heta : 0 < eta := osiiEquation66AngleAperture_pos d k
  have hTpos : 0 < T := lt_trans (by norm_num) hT
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hdT : 0 < (d : Real) * T := mul_pos hd hTpos
  have hsigma : sigma <= eta * rho / (8 * (d : Real) * T) := by
    exact osiiEquation66FirstCarrierScale_le_angle d k rho T
  have hynorm : norm y <= sigma / 4 := by
    simpa [sigma, Metric.mem_closedBall, dist_zero_right] using hy
  have hcoordSmall (i : Fin k) (mu : Fin (d + 1)) :
      |y (finProdFinEquiv (i, mu))| <
        eta *
          (center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
            (4 * (d : Real) * T)) / 2 := by
    have hcoord :
        |y (finProdFinEquiv (i, mu))| <= norm y := by
      simpa [Real.norm_eq_abs] using
        (norm_le_pi_norm y (finProdFinEquiv (i, mu)))
    let B : Real := eta * rho / (8 * (d : Real) * T)
    have hB : 0 < B := by
      dsimp [B]
      positivity
    have hcenterB : B <=
        eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (8 * (d : Real) * T) := by
      dsimp [B]
      gcongr
      exact hcenter i
    calc
      |y (finProdFinEquiv (i, mu))| <= norm y := hcoord
      _ <= sigma / 4 := hynorm
      _ <= B / 4 := by
        exact div_le_div_of_nonneg_right hsigma (by norm_num)
      _ < B := by linarith
      _ <= eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (8 * (d : Real) * T) := hcenterB
      _ = eta *
          (center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
            (4 * (d : Real) * T)) / 2 := by ring
  intro i
  let xi := osiiStep4MultiGapRealBlock (d + 1) k center i
  let zeta := osiiStep4MultiGapImaginaryBlock d k y i
  have hxi : 0 < xi 0 := by
    simpa [xi, osiiStep4MultiGapRealBlock] using
      hrho.trans_le (hcenter i)
  have hsector := osiiAxisPairCoeff_mem_narrowSector_of_small_perturbation
    T hTpos xi hxi zeta eta heta
  apply hsector
  · have hre :
        (zeta 0 / (((2 * (d : Real) * T : Real) : Complex))).re = 0 := by
      simp [zeta, osiiStep4MultiGapImaginaryBlock,
        osiiStep4ComplexOfRealImag, Complex.div_re]
    rw [hre, abs_zero]
    dsimp [xi, osiiStep4MultiGapRealBlock]
    positivity
  · intro j
    have hre : (zeta (Fin.succ j)).re = 0 := by
      simp [zeta, osiiStep4MultiGapImaginaryBlock,
        osiiStep4ComplexOfRealImag]
    rw [hre, abs_zero, zero_div]
    dsimp [xi, osiiStep4MultiGapRealBlock]
    positivity
  · have hsmall := hcoordSmall i 0
    have hdT_one : 1 < (d : Real) * T := by
      have hd_one : 1 <= (d : Real) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
      nlinarith
    have hsmall' :
        |y (finProdFinEquiv (i, (0 : Fin (d + 1))))| <
          eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) / 8 := by
      have hnum :
          0 < eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
        exact mul_pos heta (hrho.trans_le (hcenter i))
      have hsmall0 :
          |y (finProdFinEquiv (i, (0 : Fin (d + 1))))| <
            eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
              (8 * ((d : Real) * T)) := by
        convert hsmall using 1 <;> ring
      calc
        |y (finProdFinEquiv (i, (0 : Fin (d + 1))))| <
            eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
              (8 * ((d : Real) * T)) := hsmall0
        _ <= eta * center (finProdFinEquiv (i, (0 : Fin (d + 1)))) / 8 := by
          gcongr
          nlinarith
    have him :
        (zeta 0 / (((2 * (d : Real) * T : Real) : Complex))).im =
          y (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
            (2 * (d : Real) * T) := by
      simp [zeta, osiiStep4MultiGapImaginaryBlock,
        osiiStep4MultiGapRealBlock, osiiStep4ComplexOfRealImag,
        Complex.div_im]
      field_simp [hd.ne', hTpos.ne']
    rw [him, abs_div, abs_of_pos
      (show 0 < 2 * (d : Real) * T by positivity)]
    dsimp [xi, osiiStep4MultiGapRealBlock]
    convert div_lt_div_of_pos_right hsmall'
      (show 0 < 2 * (d : Real) * T by positivity) using 1 <;> ring
  · intro j
    have hsmall := hcoordSmall i (Fin.succ j)
    have him :
        (zeta (Fin.succ j)).im =
          y (finProdFinEquiv (i, Fin.succ j)) := by
      simp [zeta, osiiStep4MultiGapImaginaryBlock,
        osiiStep4MultiGapRealBlock, osiiStep4ComplexOfRealImag]
    rw [him]
    dsimp [xi, osiiStep4MultiGapRealBlock]
    convert div_lt_div_of_pos_right hsmall
      (show (0 : Real) < 2 by norm_num) using 1 <;> ring

/-- The complete multi-gap target uses at most one fixed eighth-plane of
argument, uniformly in the center, radial displacement, and common slope. -/
theorem osiiStep4MultiGapTarget_argumentBudget_lt_pi_div_eight
    (d k : Nat) [NeZero d] [NeZero k]
    {rho T : Real} (hrho : 0 < rho) (hT : 1 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (hy : y ∈ Metric.closedBall 0
      (osiiEquation66FirstCarrierScale d k rho T / 4)) :
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
      |Complex.arg
        (osiiStep4MultiGapTargetCoeff d k T center y i a)|) <
      Real.pi / 8 := by
  let eta := osiiEquation66AngleAperture d k
  have hsector :=
    osiiStep4MultiGapTargetCoeff_mem_equation66_narrowSector
      d k hrho hT center y hcenter hy
  have harg : forall i : Fin k, forall a : osiiAxisPairIndex d,
      |Complex.arg
        (osiiStep4MultiGapTargetCoeff d k T center y i a)| <
        Real.arctan eta := by
    intro i a
    have hs := hsector i a
    have hratio :
        |(osiiStep4MultiGapTargetCoeff d k T center y i a).im /
          (osiiStep4MultiGapTargetCoeff d k T center y i a).re| < eta := by
      rw [abs_div, abs_of_pos hs.1]
      exact (div_lt_iff₀ hs.1).2 hs.2
    rw [osiiLemma51_abs_arg_eq_arctan_abs_im_div_re hs.1]
    exact Real.arctan_strictMono hratio
  have hk : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  have ha :
      (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty :=
    ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true),
      Finset.mem_univ _⟩
  calc
    (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapTargetCoeff d k T center y i a)|) <
      ∑ _i : Fin k, ∑ _a : osiiAxisPairIndex d,
        Real.arctan eta :=
      Finset.sum_lt_sum_of_nonempty hk fun i _ =>
        Finset.sum_lt_sum_of_nonempty ha fun a _ => harg i a
    _ = (k : Real) * (Fintype.card (osiiAxisPairIndex d) : Real) *
        Real.arctan eta := by
      simp
      ring
    _ < Real.pi / 8 :=
      osiiEquation66AngleAperture_budget d k

/-- Fixed strip parameters with enough room for every quantitative
equation-(6.6) target. -/
noncomputable def osiiEquation66UniversalStripParameters :
    SCV.StripCompactificationParameters (Real.pi / 8) (Real.pi / 4) :=
  Classical.choice (SCV.exists_stripCompactificationParameters
    (by positivity)
    (by nlinarith [Real.pi_pos]))

/-- Reuse the universal compactification for any smaller target budget and
any wider image strip. -/
noncomputable def osiiEquation66FixedStripParameters
    {S sigma : Real}
    (hS : S <= Real.pi / 8)
    (hsigma : Real.pi / 4 <= sigma) :
    SCV.StripCompactificationParameters S sigma :=
  osiiEquation66UniversalStripParameters.weaken hS hsigma

@[simp] theorem osiiEquation66FixedStripParameters_radius
    {S sigma : Real}
    (hS : S <= Real.pi / 8)
    (hsigma : Real.pi / 4 <= sigma) :
    (osiiEquation66FixedStripParameters hS hsigma).radius =
      osiiEquation66UniversalStripParameters.radius :=
  rfl

end OSReconstruction
