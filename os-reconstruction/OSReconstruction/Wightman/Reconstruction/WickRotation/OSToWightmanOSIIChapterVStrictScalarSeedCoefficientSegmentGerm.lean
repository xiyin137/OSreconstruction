import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientGerm
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Radial coefficient germs for arbitrary logarithmic targets

The compactified coefficient germ previously exposed radial segments only
for the pure-imaginary nonnegative targets used to generate strict scalar
arguments. Full logarithmic tubes also require arbitrary real log shifts.

The local inverse of the scaled `tanh` compactification converges to division
by its slope as the compactification radius grows. A first-order estimate for
the principal complex arctangent makes this convergence uniform on any fixed
finite radial segment. Consequently, whenever the target's coefficient
imaginary `l1` mass fits a strict compactification budget, one may choose the
radius so that the complete segment from zero to that arbitrary complex
target lies in the coefficient germ.
-/

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

theorem hasDerivAt_complex_arctan_zero :
    HasDerivAt Complex.arctan 1 0 := by
  have hnum :
      HasDerivAt
        (fun z : Complex => 1 + z * I)
        I 0 := by
    convert
      (hasDerivAt_const (x := (0 : Complex)) (c := (1 : Complex))).add
        ((hasDerivAt_id' (0 : Complex)).mul_const I) using 1;
      simp
  have hden :
      HasDerivAt
        (fun z : Complex => 1 - z * I)
        (-I) 0 := by
    convert
      (hasDerivAt_const (x := (0 : Complex)) (c := (1 : Complex))).sub
        ((hasDerivAt_id' (0 : Complex)).mul_const I) using 1;
      simp
  have hquot :
      HasDerivAt
        (fun z : Complex =>
          (1 + z * I) / (1 - z * I))
        (2 * I) 0 := by
    convert hnum.div hden (by simp) using 1; ring
  have hlog :
      HasDerivAt
        (fun z : Complex =>
          Complex.log ((1 + z * I) / (1 - z * I)))
        (2 * I) 0 := by
    have hone : (1 : Complex) ∈ Complex.slitPlane := by
      simpa only [add_zero] using
        Complex.mem_slitPlane_of_norm_lt_one
          (z := (0 : Complex))
          (by
            simpa only [norm_zero] using
              (zero_lt_one : (0 : Real) < 1))
    have hcomp := HasDerivAt.comp_of_eq
      (x := (0 : Complex)) (y := (1 : Complex))
      (hh₂ := Complex.hasDerivAt_log hone)
      (hh := hquot) (hy := by simp)
    simpa only [Function.comp_apply, inv_one, one_mul] using hcomp
  change
    HasDerivAt
      (fun z : Complex =>
        -I / 2 *
          Complex.log ((1 + z * I) / (1 - z * I)))
      1 0
  have hout := hlog.const_mul (-I / 2)
  have hderiv : (-I / 2) * (2 * I) = (1 : Complex) := by
    calc
      (-I / 2) * (2 * I) = -(I * I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; norm_num
  rw [hderiv] at hout
  simpa only [Complex.arctan] using hout

theorem complex_arctan_sub_id_isLittleO :
    (fun z : Complex => Complex.arctan z - z) =o[nhds 0]
      (fun z : Complex => z) := by
  have harctan_zero : Complex.arctan 0 = 0 := by
    simp [Complex.arctan]
  simpa [harctan_zero] using
    hasDerivAt_complex_arctan_zero.isLittleO

theorem exists_norm_arctan_sub_le
    {eps : Real} (heps : 0 < eps) :
    ∃ delta : Real, 0 < delta ∧
      ∀ z : Complex, ‖z‖ < delta →
        ‖Complex.arctan z - z‖ ≤ eps * ‖z‖ := by
  have heventually :=
    complex_arctan_sub_id_isLittleO.def heps
  rw [Metric.eventually_nhds_iff] at heventually
  obtain ⟨delta, hdelta, hbound⟩ := heventually
  refine ⟨delta, hdelta, ?_⟩
  intro z hz
  apply hbound
  simpa [dist_zero_right] using hz

theorem norm_stripCompactificationLocalInverse_sub_linear_le
    {S rho eps delta : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (hbound :
      ∀ z : Complex, ‖z‖ < delta →
        ‖Complex.arctan z - z‖ ≤ eps * ‖z‖)
    {w : Complex}
    (hw : ‖w‖ / P.radius < delta) :
    ‖SCV.stripCompactificationLocalInverse P w -
        w / (P.slope : Complex)‖ ≤
      (eps / P.slope) * ‖w‖ := by
  let y : Complex :=
    (-I) * (w / (P.radius : Complex))
  have hy_norm :
      ‖y‖ = ‖w‖ / P.radius := by
    simp [y, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos P.radius_pos]
  have herr :
      ‖Complex.arctan y - y‖ ≤ eps * ‖y‖ :=
    hbound y (by simpa [hy_norm] using hw)
  have hlinear :
      (((P.radius / P.slope : Real) : Complex) * y * I) =
        w / (P.slope : Complex) := by
    dsimp [y]
    push_cast
    field_simp [P.radius_pos.ne', P.slope_pos.ne']
    rw [Complex.I_sq]
    ring
  have hdifference :
      SCV.stripCompactificationLocalInverse P w -
          w / (P.slope : Complex) =
        ((P.radius / P.slope : Real) : Complex) *
          (Complex.arctan y - y) * I := by
    rw [← hlinear]
    simp only [SCV.stripCompactificationLocalInverse, y]
    ring
  rw [hdifference, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos P.radius_pos P.slope_pos),
    Complex.norm_I, mul_one]
  calc
    (P.radius / P.slope) *
          ‖Complex.arctan y - y‖ ≤
        (P.radius / P.slope) * (eps * ‖y‖) :=
      mul_le_mul_of_nonneg_left herr
        (div_nonneg P.radius_pos.le P.slope_pos.le)
    _ = (eps / P.slope) * ‖w‖ := by
      rw [hy_norm]
      field_simp [P.radius_pos.ne', P.slope_pos.ne']

theorem osiiStrictCoefficientLocalInverseLift_mem_logDomain_of_sum_abs_im_lt
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (r : Fin n -> Complex)
    (h :
      (∑ i, |(SCV.stripCompactificationLocalInverse P (r i)).im|) <
        Real.pi / 2) :
    osiiStrictCoefficientLocalInverseLift P r ∈
      osiiAxisPairLogDomain (d := n) := by
  simp only [osiiAxisPairLogDomain, Set.mem_setOf_eq,
    osiiStrictCoefficientLocalInverseLift, Fintype.sum_prod_type]
  simpa using h

/-- Choose one large-radius compactification for an arbitrary finite complex
segment.  The useful quantitative output is separated from the doubled MZ
encoding: every point of the segment stays in the coefficient ball and its
coordinatewise local inverse has total imaginary width below pi / 2. -/
theorem exists_stripCompactificationParameters_segment_ball_inverseWidth
    {n : Nat} {S rho : Real}
    (r0 : Fin n -> Complex)
    (hS : 0 <= S)
    (hr0 : (∑ i, |(r0 i).im|) <= S)
    (hSrho : S < rho) :
    ∃ P : SCV.StripCompactificationParameters S rho,
      ∀ r, r ∈ segment Real 0 r0 ->
        r ∈ Metric.ball (0 : Fin n -> Complex) P.radius ∧
          (∑ i, |(SCV.stripCompactificationLocalInverse P (r i)).im|) <
            Real.pi / 2 := by
  let c : Real := (S + rho) / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hS_c : S < c := by
    dsimp [c]
    linarith
  have hc_rho : c < rho := by
    dsimp [c]
    linarith
  let a : Real := 2 * c / Real.pi
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_boundary :
      a * (Real.pi / 2) = c := by
    dsimp [a]
    field_simp [Real.pi_ne_zero]
  have hinverse :
      S / a < Real.pi / 2 := by
    apply (div_lt_iff₀ ha_pos).2
    calc
      S < c := hS_c
      _ = (Real.pi / 2) * a := by
        rw [mul_comm, ha_boundary]
  let margin : Real := Real.pi / 2 - S / a
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  let M : Real := ∑ i, ‖r0 i‖
  have hM : 0 <= M := by
    dsimp [M]
    exact Finset.sum_nonneg fun i _ => norm_nonneg (r0 i)
  let eta : Real := margin / (2 * (M + 1))
  have hden_eta : 0 < 2 * (M + 1) := by
    positivity
  have heta_pos : 0 < eta := by
    exact div_pos hmargin hden_eta
  have heps_pos : 0 < eta * a :=
    mul_pos heta_pos ha_pos
  obtain ⟨delta, hdelta, h_arctan⟩ :=
    exists_norm_arctan_sub_le heps_pos
  have htangent :
      ∀ᶠ R : Real in atTop,
        R * Real.tan (c / R) < rho :=
    (SCV.tendsto_mul_tan_const_div_atTop hc_pos).eventually
      (Iio_mem_nhds hc_rho)
  let lower : Real :=
    max (max 0 (2 * a)) (max M (M / delta))
  have hlarge :
      ∀ᶠ R : Real in atTop, lower < R :=
    eventually_gt_atTop lower
  rcases (hlarge.and htangent).exists with
    ⟨R, hRlarge, hRtangent⟩
  have hR_pos : 0 < R := by
    calc
      0 <= max 0 (2 * a) := le_max_left _ _
      _ <= lower := by
        exact le_max_left _ _
      _ < R := hRlarge
  have htwo_a : 2 * a < R := by
    calc
      2 * a <= max 0 (2 * a) := le_max_right _ _
      _ <= lower := by
        exact le_max_left _ _
      _ < R := hRlarge
  have hM_R : M < R := by
    calc
      M <= max M (M / delta) := le_max_left _ _
      _ <= lower := by
        exact le_max_right _ _
      _ < R := hRlarge
  have hMdelta_R : M / delta < R := by
    calc
      M / delta <= max M (M / delta) := le_max_right _ _
      _ <= lower := by
        exact le_max_right _ _
      _ < R := hRlarge
  have hM_div_R : M / R < delta := by
    apply (div_lt_iff₀ hR_pos).2
    calc
      M < R * delta :=
        (div_lt_iff₀ hdelta).1 hMdelta_R
      _ = delta * R := mul_comm _ _
  let P : SCV.StripCompactificationParameters S rho :=
    {
      slope := a
      radius := R
      slope_pos := ha_pos
      radius_pos := hR_pos
      two_mul_slope_lt_radius := htwo_a
      inverse_budget := hinverse
      tangent_budget := by
        rw [ha_boundary]
        exact hRtangent
    }
  have hetaM : eta * M < margin := by
    rw [show eta * M =
        margin * M / (2 * (M + 1)) by
      dsimp [eta]
      ring]
    apply (div_lt_iff₀ hden_eta).2
    nlinarith
  have hbudget :
      S / a + eta * M < Real.pi / 2 := by
    dsimp [margin] at hmargin hetaM
    linarith
  refine ⟨P, ?_⟩
  intro r hr
  rw [segment_eq_image_lineMap] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  have hline :
      AffineMap.lineMap
          (0 : Fin n -> Complex) r0 t =
        fun i => (t : Complex) * r0 i := by
    ext i
    simp [AffineMap.lineMap_apply_module]
  rw [hline]
  constructor
  · rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff hR_pos]
    intro i
    have hiM : ‖r0 i‖ <= M := by
      dsimp [M]
      exact Finset.single_le_sum
        (fun j _ => norm_nonneg (r0 j))
        (Finset.mem_univ i)
    calc
      ‖(t : Complex) * r0 i‖ =
          t * ‖r0 i‖ := by
        simp [abs_of_nonneg ht.1]
      _ <= ‖r0 i‖ :=
        mul_le_of_le_one_left (norm_nonneg (r0 i)) ht.2
      _ <= M := hiM
      _ < R := hM_R
  · have him_bound :
        ∀ i,
          |(SCV.stripCompactificationLocalInverse
              P ((t : Complex) * r0 i)).im| <=
            (t / a) * |(r0 i).im| +
              eta * (t * ‖r0 i‖) := by
      intro i
      let q : Complex := (t : Complex) * r0 i
      let u : Complex :=
        SCV.stripCompactificationLocalInverse P q
      have hiM : ‖r0 i‖ <= M := by
        dsimp [M]
        exact Finset.single_le_sum
          (fun j _ => norm_nonneg (r0 j))
          (Finset.mem_univ i)
      have hq_norm :
          ‖q‖ = t * ‖r0 i‖ := by
        simp [q, abs_of_nonneg ht.1]
      have hqM : ‖q‖ <= M := by
        rw [hq_norm]
        exact
          (mul_le_of_le_one_left
            (norm_nonneg (r0 i)) ht.2).trans hiM
      have hq_small : ‖q‖ / R < delta :=
        (div_le_div_of_nonneg_right hqM hR_pos.le).trans_lt
          hM_div_R
      have herr :
          ‖u - q / (a : Complex)‖ <= eta * ‖q‖ := by
        have h :=
          norm_stripCompactificationLocalInverse_sub_linear_le
            P h_arctan hq_small
        simpa [P, ha_pos.ne'] using h
      have hq_div_im :
          (q / (a : Complex)).im =
            (t / a) * (r0 i).im := by
        dsimp [q]
        rw [Complex.div_im]
        simp [Complex.normSq_apply]
        field_simp [ha_pos.ne']
      have hu_im :
          u.im =
            (q / (a : Complex)).im +
              (u - q / (a : Complex)).im := by
        simp
      calc
        |u.im| =
            |(q / (a : Complex)).im +
              (u - q / (a : Complex)).im| := by
                rw [hu_im]
        _ <=
            |(q / (a : Complex)).im| +
              |(u - q / (a : Complex)).im| :=
          abs_add_le _ _
        _ <=
            |(q / (a : Complex)).im| +
              ‖u - q / (a : Complex)‖ :=
          add_le_add (le_refl _)
            (Complex.abs_im_le_norm
              (u - q / (a : Complex)))
        _ <=
            |(q / (a : Complex)).im| +
              eta * ‖q‖ :=
          add_le_add (le_refl _) herr
        _ =
            (t / a) * |(r0 i).im| +
              eta * (t * ‖r0 i‖) := by
          rw [hq_div_im, hq_norm, abs_mul,
            abs_of_nonneg
              (div_nonneg ht.1 ha_pos.le)]
    calc
      (∑ i,
          |(SCV.stripCompactificationLocalInverse
              P ((t : Complex) * r0 i)).im|) <=
          ∑ i,
            ((t / a) * |(r0 i).im| +
              eta * (t * ‖r0 i‖)) :=
        Finset.sum_le_sum fun i _ => him_bound i
      _ =
          (t / a) * (∑ i, |(r0 i).im|) +
            eta * (t * M) := by
        simp [Finset.sum_add_distrib, M, Finset.mul_sum]
      _ <=
          (t / a) * S + eta * (t * M) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hr0
            (div_nonneg ht.1 ha_pos.le))
          (le_refl _)
      _ = t * (S / a + eta * M) := by ring
      _ <= S / a + eta * M := by
        exact mul_le_of_le_one_left
          (add_nonneg
            (div_nonneg hS ha_pos.le)
            (mul_nonneg heta_pos.le hM))
          ht.2
      _ < Real.pi / 2 := hbudget

/-- If the total target imaginary width fits a strict compactification
budget, the complete zero-to-target segment lies in the doubled strict
coefficient germ.  This is the original MZ-facing wrapper around the
reusable inverse-width estimate above. -/
theorem exists_stripCompactificationParameters_segment_subset_germDomain
    {n : Nat} {S rho : Real}
    (r0 : Fin n -> Complex)
    (hS : 0 <= S)
    (hr0 : (∑ i, |(r0 i).im|) <= S)
    (hSrho : S < rho) :
    ∃ P : SCV.StripCompactificationParameters S rho,
      segment Real 0 r0 ⊆
        osiiStrictCoefficientGermDomain P := by
  obtain ⟨P, hP⟩ :=
    exists_stripCompactificationParameters_segment_ball_inverseWidth
      r0 hS hr0 hSrho
  refine ⟨P, ?_⟩
  intro r hr
  obtain ⟨hball, hwidth⟩ := hP r hr
  exact ⟨hball,
    osiiStrictCoefficientLocalInverseLift_mem_logDomain_of_sum_abs_im_lt
      P r hwidth⟩

end OSIIChapterV
end OSReconstruction
