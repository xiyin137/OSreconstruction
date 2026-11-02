/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.SCV.HeadBlockDescent
public import OSReconstruction.SCV.DistributionalEOWKernel
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairSourcewiseMZ
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialGrowth
public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeMovingSlice
public import Mathlib.Analysis.Normed.Group.SeparationQuotient

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

/-- Recursive continuous version of integration over a finite head block. -/
noncomputable def headBlockIntegralCLM :
    (m n : Nat) ->
      SchwartzMap (Fin (m + n) -> Real) Complex →L[Complex]
        SchwartzMap (Fin n -> Real) Complex
  | 0, n => SCV.reindexSchwartzFin (Nat.zero_add n)
  | Nat.succ m, n =>
      (headBlockIntegralCLM m n).comp
        ((SCV.sliceIntegralCLM (m + n)).comp
          (SCV.reindexSchwartzFin (Nat.succ_add m n)))

theorem headBlockIntegralCLM_apply
    (m n : Nat)
    (F : SchwartzMap (Fin (m + n) -> Real) Complex) :
    headBlockIntegralCLM m n F =
      SCV.integrateHeadBlock (m := m) (n := n) F := by
  induction m with
  | zero =>
      ext u
      rw [SCV.integrateHeadBlock_apply_finAppend]
      rw [MeasureTheory.Measure.volume_pi_eq_dirac
        (ι := Fin 0) (α := fun _ => Real) (x := default)]
      simp only [headBlockIntegralCLM, SCV.reindexSchwartzFin_apply,
        MeasureTheory.integral_dirac]
      congr 1
      simpa using
        (SCV.finAppend_zero_castFinCLE
          ((SCV.castFinCLE (Nat.zero_add n)).symm u)).symm
  | succ m ih =>
      simp only [headBlockIntegralCLM, ContinuousLinearMap.comp_apply,
        SCV.sliceIntegralCLM_apply]
      rw [ih]
      exact SCV.integrateHeadBlock_sliceIntegral_reindex F

abbrev vi2SpatialHeadTailCast (d k : Nat) :
    (Fin ((k + 1) * d) -> Real) ≃L[Real]
      (Fin (d + k * d) -> Real) :=
  ContinuousLinearEquiv.piCongrLeft Real
    (fun _ : Fin (d + k * d) => Real)
    (finCongr (by ring : (k + 1) * d = d + k * d))

/-- The Section 4.3 spatial head marginal as a continuous linear map. -/
noncomputable def section43SpatialHeadMarginalCLM
    (d k : Nat) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex :=
  (section43SpatialFlatSchwartzCLE d k).symm.toContinuousLinearMap.comp
    ((headBlockIntegralCLM d (k * d)).comp
      ((SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (vi2SpatialHeadTailCast d k).symm).comp
        (section43SpatialFlatSchwartzCLE d (k + 1)).toContinuousLinearMap))

@[simp]
theorem section43SpatialHeadMarginalCLM_apply
    (d k : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex) :
    section43SpatialHeadMarginalCLM d k chi =
      section43SpatialHeadMarginal chi := by
  rw [section43SpatialHeadMarginalCLM]
  simp only [ContinuousLinearMap.comp_apply, headBlockIntegralCLM_apply]
  rfl

namespace FiniteSeminormCarrier

variable {G : Type*} [AddCommGroup G] [Module Complex G]
variable (q : Seminorm Complex G)

end FiniteSeminormCarrier

/-- A full particlewise product tensor in Section 4.3 spatial coordinates. -/
noncomputable def section43SpatialProductCMM
    (d n : Nat) :
    ContinuousMultilinearMap Complex
      (fun _ : Fin n => SchwartzMap (Fin d -> Real) Complex)
      (SchwartzMap (Section43SpatialSpace d n) Complex) :=
  (section43SpatialSchwartzParticleCLE d n).symm.toContinuousLinearMap
    |>.compContinuousMultilinearMap (SchwartzMap.productTensorMLM n)

@[simp]
theorem section43SpatialProductCMM_apply
    (d n : Nat)
    (fs : Fin n -> SchwartzMap (Fin d -> Real) Complex) :
    section43SpatialProductCMM d n fs =
      (section43SpatialSchwartzParticleCLE d n).symm
        (SchwartzMap.productTensor fs) := by
  rfl

end OSIIChapterV
end OSReconstruction
