/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.SCV.TotallyRealIdentity















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

/-- An arbitrary indexed family of compatible local time-continuation
branches. -/
structure OSIILocalTimeStageFamily
    (d k : ℕ) (ι : Type*) where
  domain : ι → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  distribution :
    ι → OSIITimeGapSpace k → OSIISpatialDistribution d k
  weaklyHolomorphic :
    ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i)
  compatible :
    ∀ i j, Set.EqOn (distribution i) (distribution j)
      (domain i ∩ domain j)

namespace OSIILocalTimeStageFamily

variable {d k : ℕ} {ι : Type*}

/-- The union of all local time-stage carriers. -/
def carrier
    (A : OSIILocalTimeStageFamily d k ι) :
    Set (OSIITimeGapSpace k) :=
  ⋃ i, A.domain i

theorem carrier_open
    (A : OSIILocalTimeStageFamily d k ι) :
    IsOpen A.carrier :=
  isOpen_iUnion A.domain_open

/-- Glue the local spatial-distribution families on their carrier union. -/
noncomputable def gluedDistribution
    (A : OSIILocalTimeStageFamily d k ι) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  SCV.glued_iUnion A.domain A.distribution

/-- The glued family agrees with each local branch on its full carrier. -/
theorem gluedDistribution_eqOn_domain
    (A : OSIILocalTimeStageFamily d k ι)
    (i : ι) :
    Set.EqOn A.gluedDistribution (A.distribution i) (A.domain i) :=
  SCV.glued_iUnion_eqOn A.compatible i

theorem gluedDistribution_apply
    (A : OSIILocalTimeStageFamily d k ι)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (fun ζ => A.gluedDistribution ζ χ) =
      SCV.glued_iUnion A.domain
        (fun i ζ => A.distribution i ζ χ) := by
  funext ζ
  simp only [gluedDistribution, SCV.glued_iUnion]
  split_ifs <;> rfl

/-- Compatible local branches remain weakly holomorphic after gluing. -/
theorem gluedDistribution_weaklyHolomorphic
    (A : OSIILocalTimeStageFamily d k ι) :
    OSIIWeaklyHolomorphicOn A.gluedDistribution A.carrier := by
  intro χ
  rw [A.gluedDistribution_apply χ]
  apply SCV.differentiableOn_glued_iUnion
  · intro ζ hζ
    exact hζ
  · exact A.domain_open
  · intro i
    exact A.weaklyHolomorphic i χ
  · intro i j ζ hζ
    exact congrArg
      (fun T : OSIISpatialDistribution d k => T χ)
      (A.compatible i j hζ)

/-- The union of the local branches is an honest Chapter V continuation
stage. -/
noncomputable def toTimeContinuationStage
    (A : OSIILocalTimeStageFamily d k ι) :
    OSIITimeContinuationStage d k where
  carrier := A.carrier
  carrier_open := A.carrier_open
  distribution := A.gluedDistribution
  weaklyHolomorphic := A.gluedDistribution_weaklyHolomorphic

end OSIILocalTimeStageFamily

end OSReconstruction
