import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Convex.Hull

/-!
# Horizontal Bounds and Convexity

Hadamard's three-lines theorem propagates a uniform bound for an entire
function from two horizontal complex slices to every slice between them. This
file packages that observation for finite-dimensional tube domains.
-/

noncomputable section

open Complex Set

namespace OSReconstruction.SCV

/-- The point with real part `x` and imaginary part `y`. -/
def horizontalPoint {ι : Type*}
    (x y : ι → ℝ) : ι → ℂ :=
  fun i => (x i : ℂ) + (y i : ℂ) * I

/-- The complex interpolation line between imaginary directions `y₀` and
`y₁`, with fixed real base `x`. Its real parameter runs through the segment
from `y₀` to `y₁`; its imaginary parameter translates the real base. -/
def horizontalSegmentLine {ι : Type*}
    (x y₀ y₁ : ι → ℝ) (w : ℂ) : ι → ℂ :=
  fun i =>
    (x i : ℂ) + (y₀ i : ℂ) * I +
      w * ((y₁ i - y₀ i : ℝ) : ℂ) * I

/-- A function is bounded on every complex interpolation strip between two
horizontal directions. The bound may depend on the real base and the two
directions. -/
def HasBoundedHorizontalSegments {ι : Type*}
    (F : (ι → ℂ) → ℂ) : Prop :=
  ∀ x y₀ y₁ : ι → ℝ,
    BddAbove
      ((norm ∘ fun w => F (horizontalSegmentLine x y₀ y₁ w)) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1)

/-- The imaginary directions on whose complete horizontal slice `F` is
bounded by `C`. -/
def horizontalBoundSet {ι : Type*}
    (F : (ι → ℂ) → ℂ) (C : ℝ) : Set (ι → ℝ) :=
  {y | ∀ x, ‖F (horizontalPoint x y)‖ ≤ C}

@[simp]
theorem horizontalSegmentLine_ofReal {ι : Type*}
    (x y₀ y₁ : ι → ℝ) (t : ℝ) :
    horizontalSegmentLine x y₀ y₁ t =
      horizontalPoint x ((1 - t) • y₀ + t • y₁) := by
  ext i
  simp [horizontalSegmentLine, horizontalPoint, Pi.smul_apply]
  ring

theorem horizontalSegmentLine_re_zero {ι : Type*}
    (x y₀ y₁ : ι → ℝ) (w : ℂ)
    (hw : w.re = 0) :
    horizontalSegmentLine x y₀ y₁ w =
      horizontalPoint
        (fun i => x i - w.im * (y₁ i - y₀ i)) y₀ := by
  ext i
  apply Complex.ext
  · simp [horizontalSegmentLine, horizontalPoint, hw]
    ring
  · simp [horizontalSegmentLine, horizontalPoint, hw]

theorem horizontalSegmentLine_re_one {ι : Type*}
    (x y₀ y₁ : ι → ℝ) (w : ℂ)
    (hw : w.re = 1) :
    horizontalSegmentLine x y₀ y₁ w =
      horizontalPoint
        (fun i => x i - w.im * (y₁ i - y₀ i)) y₁ := by
  ext i
  apply Complex.ext
  · simp [horizontalSegmentLine, horizontalPoint, hw]
    ring
  · simp [horizontalSegmentLine, horizontalPoint, hw]

@[simp]
theorem horizontalSegmentLine_im {ι : Type*}
    (x y₀ y₁ : ι → ℝ) (w : ℂ) (i : ι) :
    (horizontalSegmentLine x y₀ y₁ w i).im =
      (1 - w.re) * y₀ i + w.re * y₁ i := by
  simp [horizontalSegmentLine]
  ring

/-- The imaginary coordinates of an interpolation strip are uniformly
bounded in terms of its two endpoint directions. -/
theorem sum_sq_horizontalSegmentLine_im_le
    {ι : Type*} [Fintype ι]
    (x y₀ y₁ : ι → ℝ) (w : ℂ)
    (hw :
      w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    ∑ i, (horizontalSegmentLine x y₀ y₁ w i).im ^ 2 ≤
      ∑ i, (|y₀ i| + |y₁ i|) ^ 2 := by
  change w.re ∈ Set.Icc (0 : ℝ) 1 at hw
  apply Finset.sum_le_sum
  intro i _
  rw [horizontalSegmentLine_im]
  have ht : |w.re| ≤ 1 :=
    (abs_le.mpr ⟨by linarith [hw.1], hw.2⟩)
  have hone : |1 - w.re| ≤ 1 :=
    (abs_le.mpr ⟨by linarith [hw.2], by linarith [hw.1]⟩)
  have habs :
      |(1 - w.re) * y₀ i + w.re * y₁ i| ≤
        |y₀ i| + |y₁ i| := by
    calc
      |(1 - w.re) * y₀ i + w.re * y₁ i| ≤
          |(1 - w.re) * y₀ i| + |w.re * y₁ i| :=
        abs_add_le _ _
      _ = |1 - w.re| * |y₀ i| + |w.re| * |y₁ i| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * |y₀ i| + 1 * |y₁ i| :=
        add_le_add
          (mul_le_mul_of_nonneg_right hone (abs_nonneg _))
          (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
      _ = |y₀ i| + |y₁ i| := by ring
  have hendpoint : 0 ≤ |y₀ i| + |y₁ i| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  apply sq_le_sq.mpr
  rwa [abs_of_nonneg hendpoint]

/-- Uniform horizontal bounds of an entire function form a convex set of
imaginary directions. -/
theorem convex_horizontalBoundSet
    {ι : Type*} [Fintype ι]
    (F : (ι → ℂ) → ℂ)
    (hF : Differentiable ℂ F)
    (hseg : HasBoundedHorizontalSegments F)
    {C : ℝ} (hC : 0 < C) :
    Convex ℝ (horizontalBoundSet F C) := by
  rw [convex_iff_add_mem]
  intro y₀ hy₀ y₁ hy₁ a b ha hb hab x
  let g : ℂ → ℂ := fun w => F (horizontalSegmentLine x y₀ y₁ w)
  have hline : Differentiable ℂ (horizontalSegmentLine x y₀ y₁) := by
    rw [differentiable_pi]
    intro i
    simp only [horizontalSegmentLine]
    fun_prop
  have hg : Differentiable ℂ g :=
    hF.comp hline
  have hb_mem :
      (b : ℂ) ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    change b ∈ Set.Icc (0 : ℝ) 1
    exact ⟨hb, by linarith⟩
  have hleft :
      ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖g w‖ ≤ C := by
    intro w hw
    change w.re = 0 at hw
    rw [show g w =
      F (horizontalPoint
        (fun i => x i - w.im * (y₁ i - y₀ i)) y₀) by
          simp [g, horizontalSegmentLine_re_zero x y₀ y₁ w hw]]
    exact hy₀ _
  have hright :
      ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖g w‖ ≤ C := by
    intro w hw
    change w.re = 1 at hw
    rw [show g w =
      F (horizontalPoint
        (fun i => x i - w.im * (y₁ i - y₀ i)) y₁) by
          simp [g, horizontalSegmentLine_re_one x y₀ y₁ w hw]]
    exact hy₁ _
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      g hb_mem hg.diffContOnCl (hseg x y₀ y₁) hleft hright
  have htarget :
      horizontalPoint x (a • y₀ + b • y₁) =
        horizontalSegmentLine x y₀ y₁ b := by
    rw [horizontalSegmentLine_ofReal]
    ext i
    simp [horizontalPoint, Pi.smul_apply, show 1 - b = a by linarith]
  rw [htarget]
  change ‖g b‖ ≤ C
  calc
    ‖g b‖ ≤ C ^ (1 - b) * C ^ b := by
      simpa [g] using hthree
    _ = C := by
      rw [← Real.rpow_add hC]
      simp

/-- A uniform bound on a generating set of imaginary directions propagates to
its real convex hull. -/
theorem horizontalBound_convexHull
    {ι : Type*} [Fintype ι]
    (F : (ι → ℂ) → ℂ)
    (hF : Differentiable ℂ F)
    (hseg : HasBoundedHorizontalSegments F)
    {C : ℝ} (hC : 0 < C)
    {S : Set (ι → ℝ)}
    (hS : S ⊆ horizontalBoundSet F C) :
    convexHull ℝ S ⊆ horizontalBoundSet F C :=
  convexHull_min hS (convex_horizontalBoundSet F hF hseg hC)

end OSReconstruction.SCV
