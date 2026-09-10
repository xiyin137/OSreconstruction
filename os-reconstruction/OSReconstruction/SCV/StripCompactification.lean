/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp










noncomputable section

open Complex Filter Set Topology

namespace OSReconstruction.SCV

/-- Real part of complex `tanh`, in coordinates adapted to strip estimates. -/
theorem complex_tanh_re
    (z : Complex) :
    (Complex.tanh z).re =
      Real.sinh (2 * z.re) /
        (Real.cosh (2 * z.re) + Real.cos (2 * z.im)) := by
  rw [← Complex.re_add_im z, Complex.tanh_eq_sinh_div_cosh,
    Complex.sinh_add, Complex.cosh_add, Complex.sinh_mul_I,
    Complex.cosh_mul_I, Complex.div_re]
  simp only [Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
    sub_zero, Complex.normSq_apply]
  let x := z.re
  let y := z.im
  let D :=
    Real.cosh x * Real.cos y * (Real.cosh x * Real.cos y) +
      Real.sinh x * Real.sin y * (Real.sinh x * Real.sin y)
  have hden :
      2 * D =
        Real.cosh (2 * x) + Real.cos (2 * y) := by
    simp only [D, Real.cosh_two_mul, Real.cos_two_mul']
    nlinarith [Real.cosh_sq_sub_sinh_sq x,
      Real.sin_sq_add_cos_sq y]
  change
    Real.sinh x * Real.cos y * (Real.cosh x * Real.cos y) / D +
        Real.cosh x * Real.sin y * (Real.sinh x * Real.sin y) / D =
      Real.sinh (2 * x) /
        (Real.cosh (2 * x) + Real.cos (2 * y))
  calc
    _ = (Real.sinh x * Real.cosh x) / D := by
      rw [← add_div]
      congr 1
      calc
        Real.sinh x * Real.cos y * (Real.cosh x * Real.cos y) +
              Real.cosh x * Real.sin y * (Real.sinh x * Real.sin y) =
            Real.sinh x * Real.cosh x *
              (Real.cos y ^ 2 + Real.sin y ^ 2) := by ring
        _ = Real.sinh x * Real.cosh x := by
          rw [Real.cos_sq_add_sin_sq, mul_one]
    _ = (2 * (Real.sinh x * Real.cosh x)) / (2 * D) := by
      rw [mul_div_mul_left _ _ (two_ne_zero' Real)]
    _ = Real.sinh (2 * x) /
          (Real.cosh (2 * x) + Real.cos (2 * y)) := by
      rw [Real.sinh_two_mul, hden]
      ring

/-- Imaginary part of complex `tanh`, in coordinates adapted to strip
estimates. -/
theorem complex_tanh_im
    (z : Complex) :
    (Complex.tanh z).im =
      Real.sin (2 * z.im) /
        (Real.cosh (2 * z.re) + Real.cos (2 * z.im)) := by
  rw [← Complex.re_add_im z, Complex.tanh_eq_sinh_div_cosh,
    Complex.sinh_add, Complex.cosh_add, Complex.sinh_mul_I,
    Complex.cosh_mul_I, Complex.div_im]
  simp only [Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
    sub_zero, Complex.normSq_apply]
  let x := z.re
  let y := z.im
  let D :=
    Real.cosh x * Real.cos y * (Real.cosh x * Real.cos y) +
      Real.sinh x * Real.sin y * (Real.sinh x * Real.sin y)
  have hden :
      2 * D =
        Real.cosh (2 * x) + Real.cos (2 * y) := by
    simp only [D, Real.cosh_two_mul, Real.cos_two_mul']
    nlinarith [Real.cosh_sq_sub_sinh_sq x,
      Real.sin_sq_add_cos_sq y]
  change
    Real.cosh x * Real.sin y * (Real.cosh x * Real.cos y) / D -
        Real.sinh x * Real.cos y * (Real.sinh x * Real.sin y) / D =
      Real.sin (2 * y) /
        (Real.cosh (2 * x) + Real.cos (2 * y))
  calc
    _ = (Real.sin y * Real.cos y) / D := by
      rw [← sub_div]
      congr 1
      calc
        Real.cosh x * Real.sin y * (Real.cosh x * Real.cos y) -
              Real.sinh x * Real.cos y * (Real.sinh x * Real.sin y) =
            Real.sin y * Real.cos y *
              (Real.cosh x ^ 2 - Real.sinh x ^ 2) := by ring
        _ = Real.sin y * Real.cos y := by
          rw [Real.cosh_sq_sub_sinh_sq, mul_one]
    _ = (2 * (Real.sin y * Real.cos y)) / (2 * D) := by
      rw [mul_div_mul_left _ _ (two_ne_zero' Real)]
    _ = Real.sin (2 * y) /
          (Real.cosh (2 * x) + Real.cos (2 * y)) := by
      rw [Real.sin_two_mul, hden]
      ring

/-- On the central quarter strip, the denominator in the coordinate formulas
for complex `tanh` is strictly positive. -/
theorem complex_tanh_denominator_pos
    {z : Complex}
    (hz : |z.im| < Real.pi / 4) :
    0 <
      Real.cosh (2 * z.re) + Real.cos (2 * z.im) := by
  have him :
      |2 * z.im| < Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith
  have hcos :
      0 < Real.cos (2 * z.im) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp him)
  linarith [Real.cosh_pos (2 * z.re)]

/-- The real part of complex `tanh` stays in the open unit interval on the
central quarter strip. -/
theorem abs_complex_tanh_re_lt_one
    {z : Complex}
    (hz : |z.im| < Real.pi / 4) :
    |(Complex.tanh z).re| < 1 := by
  have hden := complex_tanh_denominator_pos hz
  have him :
      |2 * z.im| < Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith
  have hcos :
      0 < Real.cos (2 * z.im) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp him)
  have hsinh :
      |Real.sinh (2 * z.re)| <
        Real.cosh (2 * z.re) := by
    rw [Real.abs_sinh]
    calc
      Real.sinh |2 * z.re| <
          Real.cosh |2 * z.re| :=
        Real.sinh_lt_cosh _
      _ = Real.cosh (2 * z.re) :=
        Real.cosh_abs _
  rw [complex_tanh_re, abs_div, abs_of_pos hden]
  exact
    (div_lt_one hden).2
      (hsinh.trans (lt_add_of_pos_right _ hcos))

/-- The imaginary part of complex `tanh` is largest on the imaginary axis
inside the central quarter strip. -/
theorem abs_complex_tanh_im_le_abs_tan
    {z : Complex}
    (hz : |z.im| < Real.pi / 4) :
    |(Complex.tanh z).im| <= |Real.tan z.im| := by
  have hden := complex_tanh_denominator_pos hz
  have hy :
      |z.im| < Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hcos_y :
      0 < Real.cos z.im :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hy)
  have him :
      |2 * z.im| < Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    linarith
  have hcos_two :
      0 < Real.cos (2 * z.im) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp him)
  have hbase :
      0 < 1 + Real.cos (2 * z.im) := by
    linarith
  have hden_le :
      1 + Real.cos (2 * z.im) <=
        Real.cosh (2 * z.re) + Real.cos (2 * z.im) := by
    linarith [Real.one_le_cosh (2 * z.re)]
  have hquot :
      |Real.sin (2 * z.im)| /
          (1 + Real.cos (2 * z.im)) =
        |Real.tan z.im| := by
    rw [Real.sin_two_mul, Real.cos_two_mul,
      Real.tan_eq_sin_div_cos, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) <= 2),
      abs_of_pos hcos_y]
    field_simp [hcos_y.ne']
    ring
  rw [complex_tanh_im, abs_div, abs_of_pos hden]
  calc
    |Real.sin (2 * z.im)| /
          (Real.cosh (2 * z.re) + Real.cos (2 * z.im)) <=
        |Real.sin (2 * z.im)| /
          (1 + Real.cos (2 * z.im)) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hbase hden_le
    _ = |Real.tan z.im| := hquot

/-- Twice the squared norm of complex `cosh` is the positive denominator
appearing in the coordinate formulas for complex `tanh`. -/
theorem two_mul_normSq_cosh
    (z : Complex) :
    2 * Complex.normSq (Complex.cosh z) =
      Real.cosh (2 * z.re) + Real.cos (2 * z.im) := by
  rw [← Complex.re_add_im z, Complex.cosh_add,
    Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
    Complex.sinh_ofReal_re, Complex.sinh_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
    sub_zero, Complex.normSq_apply]
  rw [Real.cosh_two_mul, Real.cos_two_mul']
  nlinarith [Real.cosh_sq_sub_sinh_sq z.re,
    Real.sin_sq_add_cos_sq z.im]

/-- Complex `cosh` has no zero in the central quarter strip. -/
theorem complex_cosh_ne_zero_of_abs_im_lt_pi_div_four
    {z : Complex}
    (hz : |z.im| < Real.pi / 4) :
    Complex.cosh z ≠ 0 := by
  intro hzero
  have hpos := complex_tanh_denominator_pos hz
  have heq := two_mul_normSq_cosh z
  rw [hzero] at heq
  simp at heq
  linarith

/-- Complex `tanh` is holomorphic throughout the central quarter strip. -/
theorem differentiableAt_complex_tanh_of_abs_im_lt_pi_div_four
    {z : Complex}
    (hz : |z.im| < Real.pi / 4) :
    DifferentiableAt Complex Complex.tanh z := by
  change
    DifferentiableAt Complex
      (fun w : Complex => Complex.sinh w / Complex.cosh w) z
  exact
    Complex.differentiable_sinh.differentiableAt.div
      Complex.differentiable_cosh.differentiableAt
      (complex_cosh_ne_zero_of_abs_im_lt_pi_div_four hz)

/-- A scaled hyperbolic tangent compactifies a horizontal strip while
remaining holomorphic as long as the scaled strip stays inside the central
quarter strip. -/
def stripCompactification
    (R a : Real)
    (z : Complex) :
    Complex :=
  (R : Complex) *
    Complex.tanh (((a / R : Real) : Complex) * z)

@[simp]
theorem stripCompactification_re
    (R a : Real)
    (z : Complex) :
    (stripCompactification R a z).re =
      R *
        (Complex.tanh (((a / R : Real) : Complex) * z)).re := by
  simp [stripCompactification]

@[simp]
theorem stripCompactification_im
    (R a : Real)
    (z : Complex) :
    (stripCompactification R a z).im =
      R *
        (Complex.tanh (((a / R : Real) : Complex) * z)).im := by
  simp [stripCompactification]

@[simp]
theorem stripCompactification_scaledArgument_im
    (R a : Real)
    (z : Complex) :
    ((((a / R : Real) : Complex) * z).im) =
      (a / R) * z.im := by
  simp

@[simp]
theorem stripCompactification_ofReal
    (R a x : Real) :
    stripCompactification R a (x : Complex) =
      (R * Real.tanh ((a / R) * x) : Real) := by
  have harg :
      ((a / R : Real) : Complex) * (x : Complex) =
        (((a / R) * x : Real) : Complex) := by
    norm_cast
  rw [stripCompactification, harg, ← Complex.ofReal_tanh]
  norm_cast

@[simp]
theorem stripCompactification_ofReal_im
    (R a x : Real) :
    (stripCompactification R a (x : Complex)).im = 0 := by
  have h :=
    congrArg Complex.im
      (stripCompactification_ofReal R a x)
  calc
    (stripCompactification R a (x : Complex)).im =
        ((R * Real.tanh ((a / R) * x) : Real) : Complex).im :=
      h
    _ = 0 := rfl

/-- The real part of the scaled compactification is bounded by its real
radius. -/
theorem abs_stripCompactification_re_lt
    {R a : Real}
    (hR : 0 < R)
    {z : Complex}
    (hz :
      |(a / R) * z.im| < Real.pi / 4) :
    |(stripCompactification R a z).re| < R := by
  rw [stripCompactification_re, abs_mul, abs_of_pos hR]
  have harg :
      |((((a / R : Real) : Complex) * z).im)| <
        Real.pi / 4 := by
    rw [stripCompactification_scaledArgument_im]
    exact hz
  calc
    R *
        |(Complex.tanh (((a / R : Real) : Complex) * z)).re| <
      R * 1 :=
        mul_lt_mul_of_pos_left
          (abs_complex_tanh_re_lt_one harg) hR
    _ = R := mul_one R

/-- The imaginary part of the scaled compactification is controlled by the
ordinary tangent of the scaled strip height. -/
theorem abs_stripCompactification_im_le
    {R a : Real}
    (hR : 0 < R)
    {z : Complex}
    (hz :
      |(a / R) * z.im| < Real.pi / 4) :
    |(stripCompactification R a z).im| <=
      R * |Real.tan ((a / R) * z.im)| := by
  rw [stripCompactification_im, abs_mul, abs_of_pos hR]
  have harg :
      |((((a / R : Real) : Complex) * z).im)| <
        Real.pi / 4 := by
    rw [stripCompactification_scaledArgument_im]
    exact hz
  have him :=
    abs_complex_tanh_im_le_abs_tan harg
  rw [stripCompactification_scaledArgument_im] at him
  exact
    mul_le_mul_of_nonneg_left
      him
      hR.le

/-- The scaled compactification is holomorphic at every point whose scaled
imaginary part stays inside the central quarter strip. -/
theorem differentiableAt_stripCompactification
    {R a : Real}
    {z : Complex}
    (hz :
      |(a / R) * z.im| < Real.pi / 4) :
    DifferentiableAt Complex
      (stripCompactification R a) z := by
  let scale : Complex := (a / R : Real)
  have hscale :
      DifferentiableAt Complex
        (fun w : Complex => scale * w) z := by
    fun_prop
  have htanh :
      DifferentiableAt Complex Complex.tanh (scale * z) := by
    apply differentiableAt_complex_tanh_of_abs_im_lt_pi_div_four
    simpa [scale] using hz
  exact
    (htanh.comp z hscale).const_mul (R : Complex)

/-- The scaled tangent profile used in the strip compactification converges
to its linear slope as the compactification radius tends to infinity. -/
theorem tendsto_mul_tan_const_div_atTop
    {c : Real}
    (hc : 0 < c) :
    Tendsto
      (fun R : Real => R * Real.tan (c / R))
      atTop (nhds c) := by
  have hslope :
      Tendsto
        (fun t : Real => t⁻¹ * Real.tan t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [smul_eq_mul] using
      (Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)
        ).tendsto_slope_zero_right
  have hdiv_zero :
      Tendsto (fun R : Real => c / R) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hdiv_pos :
      ∀ᶠ R : Real in atTop, c / R ∈ Set.Ioi (0 : Real) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
    exact div_pos hc hR
  have hdiv :
      Tendsto
        (fun R : Real => c / R)
        atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdiv_zero, hdiv_pos⟩
  have hratio :
      Tendsto
        (fun R : Real =>
          (c / R)⁻¹ * Real.tan (c / R))
        atTop (nhds 1) :=
    hslope.comp hdiv
  have hmul :
      Tendsto
        (fun R : Real =>
          c * ((c / R)⁻¹ * Real.tan (c / R)))
        atTop (nhds (c * 1)) :=
    tendsto_const_nhds.mul hratio
  have hmul' :
      Tendsto
        (fun R : Real =>
          c * ((c / R)⁻¹ * Real.tan (c / R)))
        atTop (nhds c) := by
    simpa using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
  field_simp [hc.ne', hR.ne']

/-- For nonnegative arguments, `arctan` lies below the identity. -/
theorem arctan_le_self_of_nonneg
    {x : Real}
    (hx : 0 <= x) :
    Real.arctan x <= x := by
  calc
    Real.arctan x <= Real.tan (Real.arctan x) :=
      Real.le_tan
        (Real.arctan_nonneg.mpr hx)
        (Real.arctan_lt_pi_div_two x)
    _ = x := Real.tan_arctan x

/-- Quantitative parameters for compactifying the standard strip while
retaining enough imaginary budget to reach a prescribed nonnegative target. -/
structure StripCompactificationParameters
    (S rho : Real) where
  slope : Real
  radius : Real
  slope_pos : 0 < slope
  radius_pos : 0 < radius
  two_mul_slope_lt_radius : 2 * slope < radius
  inverse_budget : S / slope < Real.pi / 2
  tangent_budget :
    radius *
        Real.tan (slope * (Real.pi / 2) / radius) <
      rho

/-- Every nonnegative target budget strictly below `rho` admits strip
compactification parameters. -/
theorem exists_stripCompactificationParameters
    {S rho : Real}
    (hS : 0 <= S)
    (hSrho : S < rho) :
    Nonempty (StripCompactificationParameters S rho) := by
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
  have htangent :
      ∀ᶠ R : Real in atTop,
        R * Real.tan (c / R) < rho :=
    (tendsto_mul_tan_const_div_atTop hc_pos).eventually
      (Iio_mem_nhds hc_rho)
  have hlarge :
      ∀ᶠ R : Real in atTop,
        max 0 (2 * a) < R :=
    eventually_gt_atTop _
  rcases (hlarge.and htangent).exists with
    ⟨R, hRlarge, hRtangent⟩
  have hR_pos : 0 < R :=
    (le_max_left 0 (2 * a)).trans_lt hRlarge
  have htwo_a : 2 * a < R :=
    (le_max_right 0 (2 * a)).trans_lt hRlarge
  refine ⟨⟨a, R, ha_pos, hR_pos, htwo_a, hinverse, ?_⟩⟩
  rw [ha_boundary]
  exact hRtangent

/-- Absolute tangent is tangent of the absolute value inside the principal
strip. -/
theorem abs_tan_eq_tan_abs_of_abs_lt_pi_div_two
    {x : Real}
    (hx : |x| < Real.pi / 2) :
    |Real.tan x| = Real.tan |x| := by
  by_cases hx_nonneg : 0 <= x
  · rw [abs_of_nonneg hx_nonneg]
    rw [abs_of_nonneg]
    exact
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two
        hx_nonneg ((le_abs_self x).trans hx.le)
  · have hx_nonpos : x <= 0 := le_of_not_ge hx_nonneg
    have htan_nonpos :
        Real.tan x <= 0 :=
      Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le
        hx_nonpos (abs_lt.mp hx).1.le
    rw [abs_of_nonpos hx_nonpos, abs_of_nonpos htan_nonpos,
      Real.tan_neg]

namespace StripCompactificationParameters

/-- Uniformly rescale the image rectangle of a strip compactification.
The ratio `slope / radius`, and hence the auxiliary standard strip, is
unchanged. -/
def scale
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (c : Real)
    (hc : 0 < c) :
    StripCompactificationParameters (c * S) (c * rho) where
  slope := c * P.slope
  radius := c * P.radius
  slope_pos := mul_pos hc P.slope_pos
  radius_pos := mul_pos hc P.radius_pos
  two_mul_slope_lt_radius := by
    have h := mul_lt_mul_of_pos_left P.two_mul_slope_lt_radius hc
    nlinarith
  inverse_budget := by
    calc
      c * S / (c * P.slope) = S / P.slope := by
        field_simp [hc.ne']
      _ < Real.pi / 2 := P.inverse_budget
  tangent_budget := by
    have harg :
        c * P.slope * (Real.pi / 2) / (c * P.radius) =
          P.slope * (Real.pi / 2) / P.radius := by
      field_simp [hc.ne']
    rw [harg]
    simpa [mul_assoc] using
      (mul_lt_mul_of_pos_left P.tangent_budget hc)

@[simp]
theorem scale_slope
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (c : Real)
    (hc : 0 < c) :
    (P.scale c hc).slope = c * P.slope :=
  rfl

@[simp]
theorem scale_radius
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (c : Real)
    (hc : 0 < c) :
    (P.scale c hc).radius = c * P.radius :=
  rfl

/-- The scaled imaginary coordinate of the standard strip lies in the
central quarter strip. -/
theorem scaled_im_lt_pi_div_four
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {z : Complex}
    (hz : |z.im| < Real.pi / 2) :
    |(P.slope / P.radius) * z.im| < Real.pi / 4 := by
  have hratio_pos :
      0 < P.slope / P.radius :=
    div_pos P.slope_pos P.radius_pos
  have hratio_lt :
      P.slope / P.radius < 1 / 2 := by
    apply (div_lt_iff₀ P.radius_pos).2
    nlinarith [P.two_mul_slope_lt_radius]
  rw [abs_mul, abs_of_pos hratio_pos]
  calc
    (P.slope / P.radius) * |z.im| <
        (P.slope / P.radius) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_left hz hratio_pos
    _ < (1 / 2 : Real) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_right hratio_lt (by positivity)
    _ = Real.pi / 4 := by ring

/-- The tangent profile of every point in the standard strip stays below the
parameter's target radius. -/
theorem radius_mul_abs_tan_scaled_im_lt
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {z : Complex}
    (hz : |z.im| < Real.pi / 2) :
    P.radius *
        |Real.tan ((P.slope / P.radius) * z.im)| <
      rho := by
  have hscaled :=
    P.scaled_im_lt_pi_div_four hz
  have habs_lt_boundary :
      |(P.slope / P.radius) * z.im| <
        P.slope * (Real.pi / 2) / P.radius := by
    rw [abs_mul, abs_of_pos
      (div_pos P.slope_pos P.radius_pos)]
    calc
      (P.slope / P.radius) * |z.im| <
          (P.slope / P.radius) * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left hz
          (div_pos P.slope_pos P.radius_pos)
      _ = P.slope * (Real.pi / 2) / P.radius := by ring
  have hboundary_lt :
      P.slope * (Real.pi / 2) / P.radius <
        Real.pi / 2 := by
    have hquarter :
        P.slope * (Real.pi / 2) / P.radius <
          Real.pi / 4 := by
      have hratio_lt :
          P.slope / P.radius < 1 / 2 := by
        apply (div_lt_iff₀ P.radius_pos).2
        nlinarith [P.two_mul_slope_lt_radius]
      calc
        P.slope * (Real.pi / 2) / P.radius =
            (P.slope / P.radius) * (Real.pi / 2) := by ring
        _ < (1 / 2 : Real) * (Real.pi / 2) :=
          mul_lt_mul_of_pos_right hratio_lt (by positivity)
        _ = Real.pi / 4 := by ring
    linarith [Real.pi_pos]
  have htan_lt :
      Real.tan |(P.slope / P.radius) * z.im| <
        Real.tan
          (P.slope * (Real.pi / 2) / P.radius) :=
    Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
      (abs_nonneg _) hboundary_lt habs_lt_boundary
  rw [abs_tan_eq_tan_abs_of_abs_lt_pi_div_two
    (hscaled.trans (by linarith [Real.pi_pos]))]
  exact
    (mul_lt_mul_of_pos_left htan_lt P.radius_pos).trans
      P.tangent_budget

/-- The scaled compactification maps the standard strip into the rectangle
with real radius `radius` and imaginary radius `rho`. -/
theorem stripCompactification_mem_rectangle
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {z : Complex}
    (hz : |z.im| < Real.pi / 2) :
    |(stripCompactification P.radius P.slope z).re| <
        P.radius ∧
      |(stripCompactification P.radius P.slope z).im| <
        rho := by
  have hscaled :=
    P.scaled_im_lt_pi_div_four hz
  constructor
  · exact
      abs_stripCompactification_re_lt
        P.radius_pos hscaled
  · exact
      (abs_stripCompactification_im_le
        P.radius_pos hscaled).trans_lt
        (P.radius_mul_abs_tan_scaled_im_lt hz)

/-- The scaled compactification is holomorphic throughout the standard
strip. -/
theorem differentiableOn_stripCompactification
    {S rho : Real}
    (P : StripCompactificationParameters S rho) :
    DifferentiableOn Complex
      (stripCompactification P.radius P.slope)
      {z : Complex | |z.im| < Real.pi / 2} := by
  intro z hz
  exact
    (differentiableAt_stripCompactification
      (P.scaled_im_lt_pi_div_four hz)).differentiableWithinAt

/-- Pure-imaginary preimage of a nonnegative target under the scaled
compactification. -/
def preimage
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Real) :
    Complex :=
  ((P.radius / P.slope *
      Real.arctan (w / P.radius) : Real) : Complex) * I

@[simp]
theorem preimage_im
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Real) :
    (P.preimage w).im =
      P.radius / P.slope *
        Real.arctan (w / P.radius) := by
  simp [preimage]

@[simp]
theorem preimage_neg
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Real) :
    P.preimage (-w) = -P.preimage w := by
  simp only [preimage]
  have hdiv : -w / P.radius = -(w / P.radius) := by ring
  rw [hdiv, Real.arctan_neg]
  push_cast
  ring

/-- Replacing a signed target by its absolute value does not change the
absolute imaginary cost of its compactification preimage. -/
theorem abs_preimage_im_abs
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    (w : Real) :
    |(P.preimage |w|).im| = |(P.preimage w).im| := by
  by_cases hw : 0 <= w
  · rw [abs_of_nonneg hw]
  · have hw' : w <= 0 := le_of_not_ge hw
    rw [abs_of_nonpos hw', P.preimage_neg]
    simp

/-- The target-adapted preimages of nonnegative weights stay within the
standard logarithmic `l1` budget. -/
theorem sum_abs_preimage_im_lt
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {ι : Type} [Fintype ι]
    (w : ι -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    (∑ i, |(P.preimage (w i)).im|) <
      Real.pi / 2 := by
  have hpoint (i : ι) :
      |(P.preimage (w i)).im| <=
        w i / P.slope := by
    have hratio_nonneg :
        0 <= w i / P.radius :=
      div_nonneg (hw i) P.radius_pos.le
    have harctan_nonneg :
        0 <= Real.arctan (w i / P.radius) :=
      Real.arctan_nonneg.mpr hratio_nonneg
    rw [preimage_im, abs_of_nonneg
      (mul_nonneg
        (div_nonneg P.radius_pos.le P.slope_pos.le)
        harctan_nonneg)]
    calc
      P.radius / P.slope *
            Real.arctan (w i / P.radius) <=
          P.radius / P.slope *
            (w i / P.radius) :=
        mul_le_mul_of_nonneg_left
          (arctan_le_self_of_nonneg hratio_nonneg)
          (div_nonneg P.radius_pos.le P.slope_pos.le)
      _ = w i / P.slope := by
        field_simp [P.radius_pos.ne', P.slope_pos.ne']
  calc
    (∑ i, |(P.preimage (w i)).im|) <=
        ∑ i, w i / P.slope :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, w i) / P.slope := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ <= S / P.slope :=
      div_le_div_of_nonneg_right hsum P.slope_pos.le
    _ < Real.pi / 2 := P.inverse_budget

/-- Signed target coordinates have the same `l1` preimage estimate after
passing to their absolute values. -/
theorem sum_abs_preimage_im_lt_of_sum_abs_le
    {S rho : Real}
    (P : StripCompactificationParameters S rho)
    {ι : Type} [Fintype ι]
    (w : ι -> Real)
    (hsum : (∑ i, |w i|) <= S) :
    (∑ i, |(P.preimage (w i)).im|) < Real.pi / 2 := by
  have h := P.sum_abs_preimage_im_lt
    (fun i => |w i|) (fun i => abs_nonneg (w i)) hsum
  simpa only [P.abs_preimage_im_abs] using h

end StripCompactificationParameters

end OSReconstruction.SCV
