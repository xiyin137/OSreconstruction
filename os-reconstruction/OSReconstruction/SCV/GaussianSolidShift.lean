/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.GaussianRegularization









noncomputable section

open Complex Set
open scoped BigOperators Classical RealInnerProductSpace

namespace OSReconstruction.SCV

variable {ι : Type*} [DecidableEq ι]

/-- Keep the prescribed imaginary coordinates in `s` and set all remaining
coordinates to zero. -/
def gaussianFinsetImaginary
    (y : ι → ℝ)
    (s : Finset ι) :
    ι → ℝ :=
  fun a => if a ∈ s then y a else 0

/-- A real base is coordinatewise solid when it contains every vector whose
coordinatewise absolute values are no larger than those of one of its
points. -/
def IsCoordinatewiseSolid
    (S : Set (ι → ℝ)) : Prop :=
  ∀ ⦃y : ι → ℝ⦄, y ∈ S →
    ∀ z : ι → ℝ, (∀ a, |z a| ≤ |y a|) → z ∈ S

/-- The horizontal tube with imaginary directions in `S`. -/
def horizontalTube
    (S : Set (ι → ℝ)) :
    Set (ι → ℂ) :=
  {z | (fun a => (z a).im) ∈ S}

/-- Translate the coordinates in `s` by the prescribed imaginary vector. -/
def gaussianFinsetShift
    (F : (ι → ℂ) → ℂ)
    (y : ι → ℝ)
    (s : Finset ι)
    (z : ι → ℂ) : ℂ :=
  F (fun a =>
    z a + (gaussianFinsetImaginary y s a : ℂ) * I)

/-- The actual complex point evaluated by a partially shifted coordinate
line. -/
def gaussianFinsetCoordinatePoint
    (y : ι → ℝ)
    (s : Finset ι)
    (xBase : ι → ℝ)
    (a : ι)
    (w : ℂ) :
    ι → ℂ :=
  fun b =>
    Function.update (fun q => (xBase q : ℂ)) a w b +
      (gaussianFinsetImaginary y s b : ℂ) * I

@[simp]
theorem gaussianCoordinateLine_finsetShift
    (F : (ι → ℂ) → ℂ)
    (y : ι → ℝ)
    (s : Finset ι)
    (xBase : ι → ℝ)
    (a : ι)
    (w : ℂ) :
    gaussianCoordinateLine
        (gaussianFinsetShift F y s) xBase a w =
      F (gaussianFinsetCoordinatePoint y s xBase a w) :=
  rfl

end OSReconstruction.SCV
