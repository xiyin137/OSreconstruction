/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFrequencyReduction
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSupport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.EdgeDistribution
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialLocalMeanValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIMixedSpatialCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity
import OSReconstruction.SCV.TubeBoundaryValueExistence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.GeneralResults.FinProductIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIComplexMeanValue
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OSReconstruction.SCV.EuclideanWeylPairing
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.SchwartzTensorProduct
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
import OSReconstruction.GeneralResults.SchwartzFubini
import OSReconstruction.SCV.DistributionalEOWCutoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43WickRotateFourierLaplaceBridge

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
