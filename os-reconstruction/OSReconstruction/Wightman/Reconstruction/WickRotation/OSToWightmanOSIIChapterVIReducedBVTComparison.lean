/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFrequencyReduction
public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSupport
public import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.EdgeDistribution
public import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
public import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
public import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialLocalMeanValue
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIMixedSpatialCoordinates
public import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity
public import OSReconstruction.SCV.TubeBoundaryValueExistence
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
public import OSReconstruction.GeneralResults.FinProductIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Pi
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIComplexMeanValue
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import OSReconstruction.SCV.EuclideanWeylPairing
public import OSReconstruction.SCV.SchwartzFiniteSeminormBound
public import OSReconstruction.Wightman.SchwartzTensorProduct
public import OSReconstruction.SCV.DistributionalRepresentationUniqueness
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumSource
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional
public import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
public import OSReconstruction.GeneralResults.SchwartzFubini
public import OSReconstruction.SCV.DistributionalEOWCutoff
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz
public import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge

@[expose] public section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

namespace OSIIChapterV

/-- Reindex a full spatial particle-coordinate block into its absolute head
and reduced tail blocks. -/
def section43SpatialHeadTailIndexEquiv (d k : ℕ) :
    Fin (k + 1) × Fin d ≃ Fin d ⊕ (Fin k × Fin d) where
  toFun p := Fin.cases (Sum.inl p.2) (fun i => Sum.inr (i, p.2)) p.1
  invFun s := match s with
    | Sum.inl j => (0, j)
    | Sum.inr p => (p.1.succ, p.2)
  left_inv := by
    intro p
    rcases p with ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      rfl
  right_inv := by
    intro s
    cases s with
    | inl j => rfl
    | inr p => rfl

@[simp] theorem section43SpatialHeadTailIndexEquiv_head
    (d k : ℕ) (j : Fin d) :
    section43SpatialHeadTailIndexEquiv d k (0, j) = Sum.inl j := rfl

@[simp] theorem section43SpatialHeadTailIndexEquiv_tail
    (d k : ℕ) (i : Fin k) (j : Fin d) :
    section43SpatialHeadTailIndexEquiv d k (i.succ, j) = Sum.inr (i, j) := rfl

theorem section43SpatialFlatCLE_measurePreserving (d n : ℕ) :
    MeasurePreserving
      (section43SpatialFlatCLE d n)
      (volume : Measure (Section43SpatialSpace d n))
      (volume : Measure (Fin (n * d) → ℝ)) := by
  let h := (section43EuclideanSpaceMeasurableEquiv_measurePreserving
      (Fin n × Fin d)).trans
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin (n * d) => ℝ) finProdFinEquiv)
  convert h using 1
  funext eta i
  rw [section43SpatialFlatCLE_apply]
  change
    (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) eta)
        (finProdFinEquiv.symm i) =
      (Equiv.piCongrLeft (fun _ : Fin (n * d) => ℝ) finProdFinEquiv
        (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) eta)) i
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

end OSIIChapterV
end OSReconstruction
