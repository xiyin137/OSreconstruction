/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILocalTimeStageGluing















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The coordinatewise principal logarithm is holomorphic on the product
right half-plane. -/
theorem osiiPrincipalLog_differentiableOn_rightHalfPlane
    (k : Nat) :
    DifferentiableOn Complex
      (osiiPrincipalLog : OSIITimeGapSpace k -> Fin k -> Complex)
      (osiiTimeRightHalfPlane k) := by
  rw [differentiableOn_pi]
  intro i z hz
  have hinner :
      Differentiable Complex
        (fun w : OSIITimeGapSpace k => w i) :=
    differentiable_apply i
  simpa [osiiPrincipalLog] using
    (Complex.differentiableAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hz i)))
    ).comp_differentiableWithinAt z
      hinner.differentiableAt.differentiableWithinAt

/-- The physical right-half-plane domain on which a logarithmic stage can be
read through the principal logarithm. -/
def principalLogPushforwardCarrier
    {d k : Nat}
    (L : OSIITimeContinuationStage d k) :
    Set (OSIITimeGapSpace k) :=
  osiiTimeRightHalfPlane k ∩
    osiiPrincipalLog ⁻¹' L.carrier

theorem isOpen_principalLogPushforwardCarrier
    {d k : Nat}
    (L : OSIITimeContinuationStage d k) :
    IsOpen (principalLogPushforwardCarrier L) :=
  (osiiPrincipalLog_differentiableOn_rightHalfPlane k).continuousOn
    |>.isOpen_inter_preimage
      (isOpen_osiiTimeRightHalfPlane k)
      L.carrier_open

/-- A logarithmic continuation stage transported to physical time gaps
through the principal logarithm. -/
noncomputable def principalLogPushforwardStage
    {d k : Nat}
    (L : OSIITimeContinuationStage d k) :
    OSIITimeContinuationStage d k where
  carrier := principalLogPushforwardCarrier L
  carrier_open := isOpen_principalLogPushforwardCarrier L
  distribution :=
    fun z => L.distribution (osiiPrincipalLog z)
  weaklyHolomorphic := by
    intro chi
    simpa [Function.comp_def] using
      (L.weaklyHolomorphic chi).comp
        ((osiiPrincipalLog_differentiableOn_rightHalfPlane k).mono
          Set.inter_subset_left)
        (fun _z hz => hz.2)

@[simp] theorem principalLogPushforwardStage_carrier
    {d k : Nat}
    (L : OSIITimeContinuationStage d k) :
    (principalLogPushforwardStage L).carrier =
      principalLogPushforwardCarrier L :=
  rfl

@[simp] theorem principalLogPushforwardStage_distribution
    {d k : Nat}
    (L : OSIITimeContinuationStage d k)
    (z : OSIITimeGapSpace k) :
    (principalLogPushforwardStage L).distribution z =
      L.distribution (osiiPrincipalLog z) :=
  rfl

end OSIIChapterV

namespace OSIITimeContinuationStage.PositiveRealEdgeData

variable
  {d k : Nat} [NeZero d]
  {A B : OSIITimeContinuationStage d k}
  {W : SchwartzNPoint d k →L[Complex] Complex}
  {U : Set (Fin k -> Real)}

/-- A represented positive-real edge transfers across any stage extension
which contains the old carrier and agrees there. -/
noncomputable def ofEqOnExtension
    (E : A.PositiveRealEdgeData W U)
    (hcarrier : A.carrier ⊆ B.carrier)
    (hextends :
      Set.EqOn B.distribution A.distribution A.carrier) :
    B.PositiveRealEdgeData W U where
  orbit := E.orbit
  stageEdge := by
    intro tau htau
    have hE := E.stageEdge tau htau
    exact
      ⟨hcarrier hE.1,
        (hextends hE.1).trans hE.2⟩
  represents := E.represents
  pointwiseBounded := E.pointwiseBounded

end OSIITimeContinuationStage.PositiveRealEdgeData

end OSReconstruction
