/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import Mathlib.Order.Filter.Germ.Basic
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedPhysicalCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketContinuity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapPhysicalBlockPatch
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPhysicalSeedExistence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCompactCover
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.DenseCLM

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace SourceChronologicalCompactCoverData

variable
  {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
  {L : E →L[ℂ] SchwartzNPoint d (k + 1)}

/-- One common reduced-time window containing every translated carrier in a
domain-agnostic finite chronological source-map cover. -/
def translatedCarrierReducedTimeWindow
    (D : SourceChronologicalCompactCoverData L)
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ) :
    Set (Fin k → ℝ) :=
  letI : Fintype D.index := D.indexFintype
  ⋃ a : D.index,
    chronologicalTranslatedCarrierReducedTimeSupport (D.carrier a) T x

/-- Finite sum of sourcewise packet physical distributions associated with a
domain-agnostic chronological source-map cover. -/
noncomputable def packetPhysicalFunctional
    (D : SourceChronologicalCompactCoverData L)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered : D.AxisPairOrderedAt T)
    (Q : OSIIAxisPairPhysicalBlockPatch d k)
    (z : Q.multiGapCarrier) :
    E →L[ℂ] ℂ :=
  letI : Fintype D.index := D.indexFintype
  ∑ a : D.index,
    ((((D.carrier a).toSourcewisePacketDataAtSlope
        OS lgc T hT (hordered a)).schwartzDistributionFamily
      ).physicalDistribution Q z).comp (D.piece a)

end SourceChronologicalCompactCoverData

/-- Reduced Schwartz sources whose topological support lies in one fixed
carrier.  Compactness and strict positivity of the carrier are kept as
separate hypotheses, so the same algebraic source space can be reused by
local carrier refinements. -/
def initialPhysicalFixedCarrierSourceSubmodule
    (K : Set (NPointDomain d k)) :
    Submodule ℂ (SchwartzNPoint d k) where
  carrier := {φ |
    tsupport (φ : NPointDomain d k → ℂ) ⊆ K}
  zero_mem' := by
    intro x hx
    change x ∈ tsupport (0 : NPointDomain d k → ℂ) at hx
    rw [tsupport_zero] at hx
    exact hx.elim
  add_mem' := by
    intro φ ψ hφ hψ x hx
    have hx' :=
      tsupport_add
        (φ : NPointDomain d k → ℂ)
        (ψ : NPointDomain d k → ℂ) hx
    exact hx'.elim (fun hxφ => hφ hxφ) (fun hxψ => hψ hxψ)
  smul_mem' := by
    intro c φ hφ x hx
    apply hφ
    exact
      tsupport_smul_subset_right
        (fun _ : NPointDomain d k => c)
        (φ : NPointDomain d k → ℂ) hx

/-- The normalized reduced-test lift, restricted to one fixed reduced
carrier source submodule. -/
noncomputable def initialPhysicalFixedCarrierLiftCLM
    (K : Set (NPointDomain d k)) :
    initialPhysicalFixedCarrierSourceSubmodule (d := d) K →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (BHW.reducedTestLift k d
      (BHW.normalizedCutoffOfBump d).toSchwartz).comp
    (initialPhysicalFixedCarrierSourceSubmodule (d := d) K).subtypeL

/-- One source-independent finite cover and slope for a fixed compact
positive reduced carrier. -/
structure InitialPhysicalFixedCarrierPacketData
    (K : Set (NPointDomain d k)) where
  cover :
    SourceChronologicalCompactCoverData
      (initialPhysicalFixedCarrierLiftCLM (d := d) K)
  slope : ℝ
  slope_gt_one : 1 < slope
  ordered : cover.AxisPairOrderedAt slope

/-- The fixed-carrier packet data together with a physical patch centered at
the chosen base Euclidean point. -/
structure InitialPhysicalFixedCarrierChartData
    (K : Set (NPointDomain d k))
    (base : OSIIAxisPairMultiGapPhysicalBlockPatch d k) where
  packet : InitialPhysicalFixedCarrierPacketData (d := d) K
  patch : OSIIAxisPairMultiGapPhysicalBlockPatch d k
  patch_center :
    patch.toPhysicalBlockPatch.center =
      base.toPhysicalBlockPatch.center
  patch_slope :
    ∀ i, patch.toPhysicalBlockPatch.slope i = packet.slope

namespace InitialPhysicalFixedCarrierChartData

variable
  {K : Set (NPointDomain d k)}
  {base : OSIIAxisPairMultiGapPhysicalBlockPatch d k}

/-- The honest open physical carrier of one fixed-carrier chart. -/
def carrier
    (A : InitialPhysicalFixedCarrierChartData (d := d) K base) :
    Set (Fin (k * (d + 1)) → ℂ) :=
  A.patch.toPhysicalBlockPatch.carrier

/-- Totalized CLM-valued physical branch on one fixed-carrier chart. -/
noncomputable def distribution
    (A : InitialPhysicalFixedCarrierChartData (d := d) K base)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (z : Fin (k * (d + 1)) → ℂ) :
    initialPhysicalFixedCarrierSourceSubmodule (d := d) K →L[ℂ] ℂ :=
  if hz : z ∈ A.carrier then
    A.packet.cover.packetPhysicalFunctional
      OS lgc A.packet.slope A.packet.slope_gt_one
      A.packet.ordered A.patch.toPhysicalBlockPatch
      ⟨z, ⟨hz, A.patch.logMap_mapsTo_multiGap hz⟩⟩
  else
    0

end InitialPhysicalFixedCarrierChartData

end OSIIChapterV
end OSReconstruction
