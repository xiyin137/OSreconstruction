/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarContinuation
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.IdentityTheorem














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One bounded holomorphic chart joining zero to a prescribed ambient
target, together with the local equality needed to glue it to a bounded
predecessor. -/
structure BoundedScalarTargetChartData
    {m : Nat} {B : Real}
    (A : BoundedScalarContinuationData m B)
    (target : Fin m -> Complex) where
  domain : Set (Fin m -> Complex)
  domain_open : IsOpen domain
  domain_convex : Convex Real domain
  zero_mem_domain : (0 : Fin m -> Complex) ∈ domain
  target_mem_domain : target ∈ domain
  toFun : (Fin m -> Complex) -> Complex
  toFun_differentiableOn : DifferentiableOn Complex toFun domain
  norm_toFun_le : forall {z}, z ∈ domain -> ‖toFun z‖ <= B
  exists_open_eq_predecessor :
    ∃ U : Set (Fin m -> Complex),
      IsOpen U ∧ (0 : Fin m -> Complex) ∈ U ∧
      U ⊆ domain ∩ A.carrier ∧
      Set.EqOn toFun A.toFun U

namespace BoundedScalarTargetChartData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {target : Fin m -> Complex}

/-- Local agreement propagates to the complete connected chart/predecessor
overlap. -/
theorem toFun_eq_predecessor_on_overlap
    (D : BoundedScalarTargetChartData A target) :
    Set.EqOn D.toFun A.toFun (D.domain ∩ A.carrier) := by
  let U : Set (Fin m -> Complex) := D.domain ∩ A.carrier
  have hU_open : IsOpen U := D.domain_open.inter A.carrier_open
  have hU_connected : IsConnected U := by
    exact
      (((D.domain_convex.starConvex D.zero_mem_domain).inter
        A.carrier_starConvex).isPathConnected
          ⟨D.zero_mem_domain, A.zero_mem⟩).isConnected
  obtain ⟨V, hV_open, hV_zero, hVU, hVeq⟩ :=
    D.exists_open_eq_predecessor
  have hlocal : D.toFun =ᶠ[nhds (0 : Fin m -> Complex)] A.toFun := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨V, hV_open.mem_nhds hV_zero, hVeq⟩
  exact identity_theorem_SCV hU_open hU_connected
    (D.toFun_differentiableOn.mono Set.inter_subset_left)
    (A.differentiableOn.mono Set.inter_subset_right)
    (hVU hV_zero) hlocal

/-- A bounded holomorphic extension on an open neighborhood of the complete
zero-to-target segment supplies a bounded target chart.  Only local agreement
with the predecessor near zero is required; a convex thickening of the
compact segment provides the chart domain. -/
theorem exists_ofBoundedHolomorphicExtension
    (extensionDomain : Set (Fin m -> Complex))
    (extensionDomain_open : IsOpen extensionDomain)
    (segment_subset : segment Real 0 target ⊆ extensionDomain)
    (extension : (Fin m -> Complex) -> Complex)
    (extension_differentiableOn :
      DifferentiableOn Complex extension extensionDomain)
    (norm_extension_le : forall z, z ∈ extensionDomain ->
      ‖extension z‖ <= B)
    (agreementDomain : Set (Fin m -> Complex))
    (agreementDomain_open : IsOpen agreementDomain)
    (zero_mem_agreement : (0 : Fin m -> Complex) ∈ agreementDomain)
    (agreement_subset : agreementDomain ⊆ extensionDomain ∩ A.carrier)
    (extension_eq_predecessor :
      Set.EqOn extension A.toFun agreementDomain) :
    ∃ D : BoundedScalarTargetChartData A target,
      D.toFun = extension ∧ D.domain ⊆ extensionDomain := by
  have hcompact : IsCompact (segment Real 0 target) := by
    have hsegment :
        segment Real (0 : Fin m -> Complex) target =
          AffineMap.lineMap (0 : Fin m -> Complex) target ''
            Set.Icc (0 : Real) 1 :=
      segment_eq_image_lineMap Real (0 : Fin m -> Complex) target
    rw [hsegment]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨eps, heps, hthick⟩ :=
    hcompact.exists_thickening_subset_open
      extensionDomain_open segment_subset
  let domain := Metric.thickening eps (segment Real 0 target)
  have hzero : (0 : Fin m -> Complex) ∈ domain :=
    Metric.self_subset_thickening heps _
      (left_mem_segment Real 0 target)
  have htarget : target ∈ domain :=
    Metric.self_subset_thickening heps _
      (right_mem_segment Real 0 target)
  refine ⟨{
    domain := domain
    domain_open := Metric.isOpen_thickening
    domain_convex := (convex_segment
      (0 : Fin m -> Complex) target).thickening eps
    zero_mem_domain := hzero
    target_mem_domain := htarget
    toFun := extension
    toFun_differentiableOn :=
      extension_differentiableOn.mono hthick
    norm_toFun_le := fun {z} hz => norm_extension_le z (hthick hz)
    exists_open_eq_predecessor := ?_ }, rfl, hthick⟩
  let U := agreementDomain ∩ domain
  refine ⟨U, agreementDomain_open.inter Metric.isOpen_thickening,
    ⟨zero_mem_agreement, hzero⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨hz.2, (agreement_subset hz.1).2⟩
  · intro z hz
    exact extension_eq_predecessor hz.1

/-- Rebase a target chart along a bound-preserving extension of its
predecessor.  The old local agreement germ remains a valid agreement germ
because the extension retains the old carrier and function. -/
def rebase
    {E : BoundedScalarContinuationData m B}
    (D : BoundedScalarTargetChartData A target)
    (hsubset : A.carrier ⊆ E.carrier)
    (heq : Set.EqOn E.toFun A.toFun A.carrier) :
    BoundedScalarTargetChartData E target where
  domain := D.domain
  domain_open := D.domain_open
  domain_convex := D.domain_convex
  zero_mem_domain := D.zero_mem_domain
  target_mem_domain := D.target_mem_domain
  toFun := D.toFun
  toFun_differentiableOn := D.toFun_differentiableOn
  norm_toFun_le := D.norm_toFun_le
  exists_open_eq_predecessor := by
    obtain ⟨U, hUopen, hUzero, hUsubset, hUeq⟩ :=
      D.exists_open_eq_predecessor
    refine ⟨U, hUopen, hUzero, ?_, ?_⟩
    · intro z hz
      exact ⟨(hUsubset hz).1, hsubset (hUsubset hz).2⟩
    · intro z hz
      exact (hUeq hz).trans (heq (hUsubset hz).2).symm

end BoundedScalarTargetChartData
end OSIIChapterV
end OSReconstruction
