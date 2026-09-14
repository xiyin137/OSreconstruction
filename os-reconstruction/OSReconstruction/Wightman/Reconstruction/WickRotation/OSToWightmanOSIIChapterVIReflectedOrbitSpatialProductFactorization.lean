/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitRankGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetCutoffHullRankField












noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

@[simp]
theorem section43SpatialParticleCLE_tupleTransport
    (d : ℕ)
    {n m : ℕ}
    (h : n = m)
    (x : Section43SpatialSpace d n)
    (i : Fin m)
    (j : Fin d) :
    section43SpatialParticleCLE d m
        (section43SpatialTupleTransport d h x) i j =
      section43SpatialParticleCLE d n x (Fin.cast h.symm i) j := by
  subst m
  rfl

/-- Prepending the standard basepoint factor to a particlewise product is the
particlewise product of the prepended factor list. -/
theorem section43SpatialBasepointLift_product_eq
    (d k : Nat) [NeZero d]
    (rho : SchwartzMap (Fin d -> Real) Complex)
    (fs : Fin k -> SchwartzMap (Fin d -> Real) Complex) :
    section43SpatialBasepointLiftCLM d k rho
        (section43SpatialProductCMM d k fs) =
      section43SpatialProductCMM d (k + 1) (Fin.cons rho fs) := by
  apply (section43SpatialSchwartzParticleCLE d (k + 1)).injective
  ext x
  simp [section43SpatialBasepointLiftCLM,
    section43SpatialProductCMM, SchwartzMap.productTensor_succ]

/-- An arbitrary complex particlewise product is exactly the reflected
two-block product obtained by conjugating its left factors before insertion
into `section43TwoBlockSpatialProduct`. -/
theorem section43TwoBlockSpatialProduct_particleProducts_eq
    (d n m : Nat) [NeZero d]
    (fs : Fin (n + m) -> SchwartzMap (Fin d -> Real) Complex) :
    section43TwoBlockSpatialProduct
        (section43SpatialProductCMM d n (fun a =>
          (fs (Fin.castAdd m a)).conj))
        (section43SpatialProductCMM d m (fun b =>
          fs (Fin.natAdd n b))) =
      section43SpatialProductCMM d (n + m) fs := by
  ext eta
  rw [section43TwoBlockSpatialProduct_apply,
    section43SpatialProductCMM_apply,
    section43SpatialProductCMM_apply,
    section43SpatialProductCMM_apply]
  simp only [section43SpatialSchwartzParticleCLE_symm_apply,
    SchwartzMap.productTensor_apply, SchwartzMap.conj_apply, map_prod,
    starRingEnd_apply, star_star]
  rw [Fin.prod_univ_add]
  apply congrArg₂ (fun x y : Complex => x * y)
  · apply Finset.prod_congr rfl
    intro a _ha
    apply congrArg (fs (Fin.castAdd m a))
    funext j
    exact section43TwoBlockSpatialSplitCLE_fst_apply eta a j
  · apply Finset.prod_congr rfl
    intro b _hb
    apply congrArg (fs (Fin.natAdd n b))
    funext j
    exact section43TwoBlockSpatialSplitCLE_snd_apply eta b j

/-- Pulling a common-arity particlewise product into a generator's native
split coordinates only reindexes its particle factors. -/
theorem generatorSplitSpatialPullbackCLM_product_eq_reindex
    (d k : Nat) [NeZero d]
    (i : GeneratorIndex k)
    (fs : Fin (k + 1) -> SchwartzMap (Fin d -> Real) Complex) :
    generatorSplitSpatialPullbackCLM (d := d) i
        (section43SpatialProductCMM d (k + 1) fs) =
      section43SpatialProductCMM d (i.n + i.m) (fun c =>
        fs (Fin.cast i.absoluteCard_eq.symm c)) := by
  ext eta
  rw [generatorSplitSpatialPullbackCLM,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43SpatialProductCMM_apply]
  simp only [Function.comp_apply]
  rw [
    section43SpatialSchwartzParticleCLE_symm_apply,
    SchwartzMap.productTensor_apply,
    section43SpatialProductCMM_apply,
    section43SpatialSchwartzParticleCLE_symm_apply,
    SchwartzMap.productTensor_apply]
  let F : Fin (k + 1) -> Complex := fun c =>
    fs c (section43SpatialParticleCLE d (k + 1)
      (generatorSplitToAbsoluteSpatialCLE i eta) c)
  calc
    (∏ c, F c) =
        ∏ c : Fin (i.n + i.m),
          F (Fin.cast i.absoluteCard_eq.symm c) := by
      exact Fintype.prod_equiv
        (finCongr i.absoluteCard_eq)
        F
        (fun c : Fin (i.n + i.m) =>
          F (Fin.cast i.absoluteCard_eq.symm c))
        (fun c => by simp)
    _ = ∏ c : Fin (i.n + i.m),
        fs (Fin.cast i.absoluteCard_eq.symm c)
          (section43SpatialParticleCLE d (i.n + i.m) eta c) := by
      apply Finset.prod_congr rfl
      intro c _hc
      dsimp [F]
      apply congrArg (fs (Fin.cast i.absoluteCard_eq.symm c))
      funext j
      rw [generatorSplitToAbsoluteSpatialCLE_apply]
      simp

/-- A common particlewise product is a single left/right spatial product in
every native generator split.  The left factors are conjugated before being
passed to `section43TwoBlockSpatialProduct`, which conjugates the assembled
left block once more. -/
theorem generatorSplitSpatialPullbackCLM_product_eq_twoBlock
    (d k : Nat) [NeZero d]
    (i : GeneratorIndex k)
    (fs : Fin (k + 1) -> SchwartzMap (Fin d -> Real) Complex) :
    generatorSplitSpatialPullbackCLM (d := d) i
        (section43SpatialProductCMM d (k + 1) fs) =
      section43TwoBlockSpatialProduct
        (section43SpatialProductCMM d i.n (fun a =>
          (fs (i.leftAbsoluteIndex a)).conj))
        (section43SpatialProductCMM d i.m (fun b =>
          fs (i.rightAbsoluteIndex b))) := by
  rw [generatorSplitSpatialPullbackCLM_product_eq_reindex]
  symm
  simpa [GeneratorIndex.leftAbsoluteIndex,
    GeneratorIndex.rightAbsoluteIndex] using
    section43TwoBlockSpatialProduct_particleProducts_eq
      d i.n i.m (fun c => fs (Fin.cast i.absoluteCard_eq.symm c))

end OSIIChapterV
end OSReconstruction
