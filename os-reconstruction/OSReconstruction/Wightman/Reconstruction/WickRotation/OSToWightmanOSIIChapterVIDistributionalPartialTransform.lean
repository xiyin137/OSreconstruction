/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelFullSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolutionSupport


















noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

/-- A distribution on the full real `k`-block spacetime for every full
imaginary displacement. -/
abbrev OSIIImaginarySliceDistributionFamily (d k : ℕ) :=
  (Fin (k * (d + 1)) → ℝ) → (SchwartzNPoint d k →L[ℂ] ℂ)

/-- Distributional form of the OS-II partial transform. -/
noncomputable def osiiStep4DistributionalPartialConvolutionTransform
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ) : ℂ :=
  B y (osiiStep4CenteredPartialConvolutionKernelFullSource
    d k hrho center y y')

/-- Representation localized in both variables relevant to equation `(6.6)`:
the imaginary displacement lies in `Y`, and the real Schwartz test is
supported in `X`.  This is the natural interface for a density known only on
a local forward-tube patch. -/
def OSIIImaginarySliceDistributionFamily.RepresentsOnSupport
    (B : OSIIImaginarySliceDistributionFamily d k)
    (Y X : Set (Fin (k * (d + 1)) → ℝ))
    (F : (Fin (k * (d + 1)) → ℂ) → ℂ) : Prop :=
  ∀ y ∈ Y, ∀ phi : SchwartzNPoint d k,
    Function.support (flattenSchwartzNPoint (d := d) phi) ⊆ X ->
      B y phi =
      ∫ x : Fin (k * (d + 1)) → ℝ,
        F (osiiStep4ComplexOfRealImag x y) *
          flattenSchwartzNPoint (d := d) phi x

/-- Support-local representation is sufficient for the partial transform:
only the centered kernel used in this pairing must be supported in the real
carrier `X`. -/
theorem
    osiiStep4DistributionalPartialConvolutionTransform_eq_partialTransform_of_representsOnSupport
    (B : OSIIImaginarySliceDistributionFamily d k)
    (F : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (Y X : Set (Fin (k * (d + 1)) → ℝ))
    (hB : B.RepresentsOnSupport Y X F)
    {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ)
    (hy : y ∈ Y)
    (hsource : Function.support
      (flattenSchwartzNPoint (d := d)
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y')) ⊆ X) :
    osiiStep4DistributionalPartialConvolutionTransform
        B hrho center y y' =
      osiiStep4PartialConvolutionTransform
        (osiiStep4FullBlockRadialG (d + 1) k rho) F
        (osiiStep4ComplexOfRealImag center 0) y y' := by
  rw [osiiStep4DistributionalPartialConvolutionTransform,
    hB y hy _ hsource]
  simp only [flatten_osiiStep4CenteredPartialConvolutionKernelFullSource]
  let H : (Fin (k * (d + 1)) → ℝ) → ℂ := fun u =>
    F (osiiStep4ComplexOfRealImag u y) *
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (d + 1) k hrho center y y' u
  calc
    (∫ u : Fin (k * (d + 1)) → ℝ,
        F (osiiStep4ComplexOfRealImag u y) *
          osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
            (d + 1) k hrho center y y' u) =
        ∫ x : Fin (k * (d + 1)) → ℝ, H (x + center) := by
      exact (integral_add_right_eq_self H center).symm
    _ = osiiStep4PartialConvolutionTransform
        (osiiStep4FullBlockRadialG (d + 1) k rho) F
        (osiiStep4ComplexOfRealImag center 0) y y' := by
      rw [osiiStep4PartialConvolutionTransform]
      apply integral_congr_ae
      filter_upwards with x
      have hcomplex :
          osiiStep4ComplexOfRealImag (x + center) y =
            osiiStep4ComplexOfRealImag center 0 +
              osiiStep4ComplexOfRealImag x y := by
        ext a
        simp [osiiStep4ComplexOfRealImag]
        ring
      simp only [H]
      rw [hcomplex]
      simp [
        osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply]

theorem
    osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_auxImaginary_coord
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ)
    (i : Fin k) (mu : Fin (d + 1))
    (hcoord : rho / 8 ≤ |y' (finProdFinEquiv (i, mu))|) :
    osiiStep4DistributionalPartialConvolutionTransform
        B hrho center y y' = 0 := by
  have hsource :
      osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y' = 0 := by
    ext x
    rw [osiiStep4CenteredPartialConvolutionKernelFullSource_apply]
    rw [osiiStep4PartialConvolutionKernel_eq_zero_of_auxImaginary_coord
      (d + 1) k hrho _ y y' i mu hcoord]
    rfl
  simp [osiiStep4DistributionalPartialConvolutionTransform, hsource]

theorem
    osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_imaginaryDifference_coord
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ)
    (i : Fin k) (mu : Fin (d + 1))
    (hcoord : rho / 8 ≤
      |y (finProdFinEquiv (i, mu)) -
        y' (finProdFinEquiv (i, mu))|) :
    osiiStep4DistributionalPartialConvolutionTransform
        B hrho center y y' = 0 := by
  have hsource :
      osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y' = 0 := by
    ext x
    rw [osiiStep4CenteredPartialConvolutionKernelFullSource_apply]
    rw [osiiStep4PartialConvolutionKernel_eq_zero_of_imaginaryDifference_coord
      (d + 1) k hrho _ y y' i mu hcoord]
    rfl
  simp [osiiStep4DistributionalPartialConvolutionTransform, hsource]

/-- The distributional partial transform has exactly the same auxiliary
imaginary support as the pointwise formula. -/
theorem osiiStep4DistributionalPartialConvolutionTransform_support_subset
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) → ℝ) :
    Function.support (fun p :
        (Fin (k * (d + 1)) → ℝ) × (Fin (k * (d + 1)) → ℝ) =>
      osiiStep4DistributionalPartialConvolutionTransform
        B hrho center p.1 p.2) ⊆
      osiiStep4PartialConvolutionImaginarySupport (d + 1) k rho := by
  intro p hp i mu
  constructor
  · by_contra hnot
    exact hp
      (osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_auxImaginary_coord
        B hrho center p.1 p.2 i mu (le_of_not_gt hnot))
  · by_contra hnot
    exact hp
      (osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_imaginaryDifference_coord
        B hrho center p.1 p.2 i mu (le_of_not_gt hnot))

/-- The coordinatewise imaginary support is contained in the compact box
used by the ordinary-volume equation-(6.6) integral. -/
theorem
    osiiStep4DistributionalPartialConvolutionTransform_support_subset_closedImaginaryBox
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) → ℝ) :
    Function.support (fun p :
        (Fin (k * (d + 1)) → ℝ) ×
          (Fin (k * (d + 1)) → ℝ) =>
      osiiStep4DistributionalPartialConvolutionTransform
        B hrho center p.1 p.2) ⊆
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) k rho := by
  intro p hp
  have hsupp :=
    osiiStep4DistributionalPartialConvolutionTransform_support_subset
      B hrho center hp
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply le_of_lt
    rw [pi_norm_lt_iff (by positivity : 0 < rho / 4)]
    intro a
    let i : Fin k := (finProdFinEquiv.symm a).1
    let mu : Fin (d + 1) := (finProdFinEquiv.symm a).2
    have ha : finProdFinEquiv (i, mu) = a :=
      finProdFinEquiv.apply_symm_apply a
    have haux := (hsupp i mu).1
    have hdiff := (hsupp i mu).2
    calc
      ‖p.1 a‖ = |(p.1 a - p.2 a) + p.2 a| := by
        rw [Real.norm_eq_abs]
        congr 1
        ring
      _ ≤ |p.1 a - p.2 a| + |p.2 a| := abs_add_le _ _
      _ < rho / 8 + rho / 8 := by
        simpa only [ha] using add_lt_add hdiff haux
      _ = rho / 4 := by ring
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply le_of_lt
    rw [pi_norm_lt_iff (by positivity : 0 < rho / 8)]
    intro a
    let i : Fin k := (finProdFinEquiv.symm a).1
    let mu : Fin (d + 1) := (finProdFinEquiv.symm a).2
    have ha : finProdFinEquiv (i, mu) = a :=
      finProdFinEquiv.apply_symm_apply a
    simpa only [Real.norm_eq_abs, ha] using (hsupp i mu).1

/-- Outside the first projection of the compact imaginary support box, the
distributional partial transform vanishes. -/
theorem
    osiiStep4DistributionalPartialConvolutionTransform_eq_zero_of_not_mem_first_closedBall
    (B : OSIIImaginarySliceDistributionFamily d k)
    {rho : ℝ} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → ℝ)
    (hy : y ∉ Metric.closedBall 0 (rho / 4)) :
    osiiStep4DistributionalPartialConvolutionTransform
        B hrho center y y' = 0 := by
  exact eq_zero_of_support_subset_prod_left
    (fun p => osiiStep4DistributionalPartialConvolutionTransform
      B hrho center p.1 p.2)
    (Metric.closedBall 0 (rho / 4))
    (Metric.closedBall 0 (rho / 8))
    (osiiStep4DistributionalPartialConvolutionTransform_support_subset_closedImaginaryBox
      B hrho center) y y' hy

end OSReconstruction
