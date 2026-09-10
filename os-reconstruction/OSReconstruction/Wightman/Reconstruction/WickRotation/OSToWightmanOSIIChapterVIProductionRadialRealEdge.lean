/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRealEdgeCauchy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialGevrey









noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction

def osiiProductionRealRadialPoint
    {m : Nat} (x : EuclideanSpace Real (Fin m)) (v : Fin m → Real) :
    EuclideanSpace Real (Fin m) :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin m => Real)).symm
    ((fun i => x i) + v)

@[simp]
theorem osiiProductionRealRadialPoint_zero
    {m : Nat} (x : EuclideanSpace Real (Fin m)) :
    osiiProductionRealRadialPoint x 0 = x := by
  ext i
  simp [osiiProductionRealRadialPoint]

def osiiProductionRealRadialSlice
    {m : Nat} (x : EuclideanSpace Real (Fin m)) (v : Fin m → Real) :
    Complex :=
  (Real.smoothTransition
    (2 - ‖osiiProductionRealRadialPoint x v‖) : Complex) -
      osiiProductionRadialAnnulusBaseline x

theorem osiiProductionComplexRadialBump_realEdge_eventuallyEq
    {m : Nat}
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2) :
    (fun v : Fin m → Real =>
      OSIIChapterV.realAffineSlice
        (fun z => osiiProductionComplexRadialBump z -
          osiiProductionRadialAnnulusBaseline x)
        (fun i => (x i : Complex)) v) =ᶠ[𝓝 0]
      osiiProductionRealRadialSlice x := by
  have hpoint_cont :
      Continuous (osiiProductionRealRadialPoint x) := by
    unfold osiiProductionRealRadialPoint
    exact
      (PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin m => Real)).symm.continuous.comp
          (continuous_const.add continuous_id)
  have hnorm_cont :
      Continuous (fun v : Fin m → Real =>
        ‖osiiProductionRealRadialPoint x v‖) :=
    continuous_norm.comp hpoint_cont
  have hlower_eventually :
      ∀ᶠ v : Fin m → Real in 𝓝 0,
        1 < ‖osiiProductionRealRadialPoint x v‖ := by
    apply (isOpen_Ioi.preimage hnorm_cont).mem_nhds
    simpa using hx_lower
  have hupper_eventually :
      ∀ᶠ v : Fin m → Real in 𝓝 0,
        ‖osiiProductionRealRadialPoint x v‖ < 2 := by
    apply (isOpen_Iio.preimage hnorm_cont).mem_nhds
    simpa using hx_upper
  filter_upwards [hlower_eventually, hupper_eventually]
    with v hlower hupper
  have hcoords :
      (fun i => (x i : Complex)) +
          OSIIChapterV.realCoordinateEmbeddingCLM m v =
        fun i =>
          (osiiProductionRealRadialPoint x v i : Complex) := by
    funext i
    simp [osiiProductionRealRadialPoint]
  rw [OSIIChapterV.realAffineSlice, hcoords]
  dsimp [osiiProductionRealRadialSlice]
  rw [osiiProductionComplexRadialBump_real _ hlower hupper]

end OSReconstruction
