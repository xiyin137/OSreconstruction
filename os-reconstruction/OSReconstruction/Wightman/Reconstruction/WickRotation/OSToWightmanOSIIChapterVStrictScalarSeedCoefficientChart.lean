/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedLogarithmicDomains
public import OSReconstruction.SCV.GaussianSolidShift
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedScalarSeeds
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedScalarSeedStage
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicCoordinates
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope

@[expose] public section

noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The complex coefficient chart associated to a finite family of real
strict scalar seeds. -/
def osiiStrictScalarSeedCoefficientMap
    {ι : Type} [Fintype ι] {k : Nat}
    (seed : ι -> Fin k -> Real)
    (r : ι -> Complex) :
    Fin k -> Complex :=
  fun j => ∑ i, r i * (seed i j : Complex)

/-- The finite seed coefficient chart is entire. -/
theorem osiiStrictScalarSeedCoefficientMap_differentiable
    {ι : Type} [Fintype ι] {k : Nat}
    (seed : ι -> Fin k -> Real) :
    Differentiable Complex
      (osiiStrictScalarSeedCoefficientMap seed) := by
  rw [differentiable_pi]
  intro j
  exact Differentiable.fun_sum fun i _ =>
    (differentiable_apply i).mul (differentiable_const _)

/-- The imaginary part of the coefficient chart is the corresponding real
linear combination of the seed arguments. -/
theorem osiiStrictScalarSeedCoefficientMap_im
    {ι : Type} [Fintype ι] {k : Nat}
    (seed : ι -> Fin k -> Real)
    (r : ι -> Complex) :
    (fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im) =
      ∑ i, (r i).im • seed i := by
  funext j
  simp [osiiStrictScalarSeedCoefficientMap,
    Finset.sum_apply, Pi.smul_apply]

/-- The pure-imaginary coefficient point associated to real weights. -/
def osiiStrictScalarSeedCoefficientTarget
    {ι : Type} (w : ι -> Real) :
    ι -> Complex :=
  fun i => (w i : Complex) * I

/-- At the pure-imaginary weight point, the coefficient chart evaluates to
the pure-imaginary argument represented by those weights. -/
theorem osiiStrictScalarSeedCoefficientMap_target
    {ι : Type} [Fintype ι]
    {k : Nat}
    (w : ι -> Real)
    (seed : ι -> Fin k -> Real)
    (x : Fin k -> Real)
    (hcombination : (∑ i, w i • seed i) = x) :
    osiiStrictScalarSeedCoefficientMap seed
        (osiiStrictScalarSeedCoefficientTarget w) =
      fun j => (x j : Complex) * I := by
  funext j
  apply Complex.ext
  · simp [osiiStrictScalarSeedCoefficientMap,
      osiiStrictScalarSeedCoefficientTarget]
  · have hj := congrFun hcombination j
    simpa [osiiStrictScalarSeedCoefficientMap,
      osiiStrictScalarSeedCoefficientTarget,
      Finset.sum_apply, Pi.smul_apply] using hj

namespace GeneratedScalarSeedStageLevelSuccessorData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}

end GeneratedScalarSeedStageLevelSuccessorData

end OSIIChapterV
end OSReconstruction
