/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LocallyUniformLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOverlap




















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Sourcewise data sufficient to assemble the scalar Chapter V generator
shells into a gluable family of spatial distributions.

The approximants retain continuous linearity in the spatial Schwartz test.
Their locally uniform scalar limits need not be assumed continuous: that
continuity is recovered pointwise by Banach-Steinhaus. -/
structure GeneratorSpatialApproximationFamily (d k : ℕ) where
  domain : GeneratorIndex k → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  approximation :
    GeneratorIndex k → ℕ →
      OSIITimeGapSpace k → OSIISpatialDistribution d k
  approximation_weaklyHolomorphic :
    ∀ i N, OSIIWeaklyHolomorphicOn (approximation i N) (domain i)
  scalarLimit :
    GeneratorIndex k → OSIITimeGapSpace k →
      SchwartzMap (Section43SpatialSpace d k) ℂ → ℂ
  locallyUniform :
    ∀ i χ,
      TendstoLocallyUniformlyOn
        (fun N z => approximation i N z χ)
        (fun z => scalarLimit i z χ)
        atTop (domain i)

namespace GeneratorSpatialApproximationFamily

variable {d k : ℕ}

/-- Construct the sourcewise assembly data directly from locally uniform
Cauchy estimates for the finite spatial-distribution shells.

Completeness of `ℂ` supplies each scalar limit.  No continuity of the selected
limit in the spatial test is assumed here; `distribution` recovers it later
from pointwise limits of continuous linear functionals. -/
noncomputable def ofLocallyUniformCauchy
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (approximation :
      GeneratorIndex k → ℕ →
        OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (approximation_weaklyHolomorphic :
      ∀ i N, OSIIWeaklyHolomorphicOn (approximation i N) (domain i))
    (locallyUniformCauchy :
      ∀ i χ z, z ∈ domain i →
        ∃ V ∈ 𝓝[domain i] z,
          UniformCauchySeqOn
            (fun N w => approximation i N w χ) atTop V) :
    GeneratorSpatialApproximationFamily d k :=
  let hlimit := fun i χ =>
    SCV.exists_tendstoLocallyUniformlyOn_of_locally_uniformCauchy
      (locallyUniformCauchy i χ)
  { domain := domain
    domain_open := domain_open
    approximation := approximation
    approximation_weaklyHolomorphic := approximation_weaklyHolomorphic
    scalarLimit := fun i z χ => Classical.choose (hlimit i χ) z
    locallyUniform := fun i χ => Classical.choose_spec (hlimit i χ) }

/-- The real-edge obligation for one sourcewise approximation family.

It is kept separate from the analytic assembly data because identification
with the A0 orbit and connectedness of complex overlaps are distinct
mathematical steps. -/
structure CommonPositiveRealEdgeData
    (A : GeneratorSpatialApproximationFamily d k) where
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  orbit : (Fin k → ℝ) → OSIISpatialDistribution d k
  scalarLimit_realEdge :
    ∀ i τ, τ ∈ realRegion →
      osiiPositiveRealTimeEmbed τ ∈ A.domain i ∧
        ∀ χ, A.scalarLimit i (osiiPositiveRealTimeEmbed τ) χ = orbit τ χ

/-- Local uniform convergence supplies the pointwise scalar convergence used
to reconstruct the limiting spatial distribution. -/
theorem pointwise_tendsto
    (A : GeneratorSpatialApproximationFamily d k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ A.domain i)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto (fun N => A.approximation i N z χ) atTop
      (𝓝 (A.scalarLimit i z χ)) :=
  (A.locallyUniform i χ).tendsto_at hz

/-- The canonical spatial distribution obtained from the sourcewise scalar
limit on one generator domain.  Its value is set to zero off the domain,
where no continuation claim is made. -/
noncomputable def distribution
    (A : GeneratorSpatialApproximationFamily d k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    OSIISpatialDistribution d k :=
  if hz : z ∈ A.domain i then
    osiiSpatialDistributionOfPointwiseLimit
      (fun N => A.approximation i N z)
      (A.scalarLimit i z)
      (A.pointwise_tendsto i z hz)
  else
    0

/-- On its generator domain, the assembled distribution evaluates to the
prescribed scalar shell. -/
theorem distribution_apply_of_mem
    (A : GeneratorSpatialApproximationFamily d k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ A.domain i)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    A.distribution i z χ = A.scalarLimit i z χ := by
  rw [distribution, dif_pos hz]
  exact osiiSpatialDistributionOfPointwiseLimit_apply
    (fun N => A.approximation i N z)
    (A.scalarLimit i z)
    (A.pointwise_tendsto i z hz) χ

/-- Locally uniform limits of the finite distribution-valued approximants
form a weakly holomorphic spatial-distribution family. -/
theorem distribution_weaklyHolomorphic
    (A : GeneratorSpatialApproximationFamily d k)
    (i : GeneratorIndex k) :
    OSIIWeaklyHolomorphicOn (A.distribution i) (A.domain i) := by
  intro χ
  have hlimit :
      DifferentiableOn ℂ (fun z => A.scalarLimit i z χ) (A.domain i) :=
    (A.locallyUniform i χ).differentiableOn_finite
      (Filter.Eventually.of_forall fun N =>
        A.approximation_weaklyHolomorphic i N χ)
      (A.domain_open i)
  exact hlimit.congr fun z hz =>
    A.distribution_apply_of_mem i z hz χ

/-- The scalar common edge becomes equality of the assembled spatial
distributions with the named A0 orbit. -/
theorem distribution_commonPositiveRealEdge
    (A : GeneratorSpatialApproximationFamily d k) :
    ∀ (E : A.CommonPositiveRealEdgeData) i τ, τ ∈ E.realRegion →
      osiiPositiveRealTimeEmbed τ ∈ A.domain i ∧
        A.distribution i (osiiPositiveRealTimeEmbed τ) = E.orbit τ := by
  intro E i τ hτ
  have hedge := E.scalarLimit_realEdge i τ hτ
  refine ⟨hedge.1, ?_⟩
  apply ContinuousLinearMap.ext
  intro χ
  rw [A.distribution_apply_of_mem i _ hedge.1 χ]
  exact hedge.2 χ

namespace CommonPositiveRealEdgeData

/-- Convex generator domains have connected pairwise overlaps because the
common positive-real edge supplies a point in every overlap. -/
theorem overlap_connected_of_convex
    (A : GeneratorSpatialApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData)
    (hconvex : ∀ i, Convex ℝ (A.domain i)) :
    ∀ i j, IsConnected (A.domain i ∩ A.domain j) := by
  intro i j
  apply ((hconvex i).inter (hconvex j)).isConnected
  obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
  exact
    ⟨osiiPositiveRealTimeEmbed τ,
      (E.scalarLimit_realEdge i τ hτ).1,
      (E.scalarLimit_realEdge j τ hτ).1⟩

/-- If the finite spatial-distribution approximants converge on the real
slice to the A0 orbit, uniqueness of scalar limits identifies the locally
uniform complex shell with that orbit. -/
def ofApproximationTendsto
    (A : GeneratorSpatialApproximationFamily d k)
    (realRegion : Set (Fin k → ℝ))
    (realRegion_open : IsOpen realRegion)
    (realRegion_nonempty : realRegion.Nonempty)
    (orbit : (Fin k → ℝ) → OSIISpatialDistribution d k)
    (real_mem :
      ∀ i τ, τ ∈ realRegion →
        osiiPositiveRealTimeEmbed τ ∈ A.domain i)
    (approximation_tendsto_orbit :
      ∀ i τ, τ ∈ realRegion →
        ∀ χ,
          Tendsto
            (fun N =>
              A.approximation i N
                (osiiPositiveRealTimeEmbed τ) χ)
            atTop (𝓝 (orbit τ χ))) :
    A.CommonPositiveRealEdgeData where
  realRegion := realRegion
  realRegion_open := realRegion_open
  realRegion_nonempty := realRegion_nonempty
  orbit := orbit
  scalarLimit_realEdge := by
    intro i τ hτ
    have hmem := real_mem i τ hτ
    refine ⟨hmem, fun χ => ?_⟩
    exact tendsto_nhds_unique
      (A.pointwise_tendsto i (osiiPositiveRealTimeEmbed τ) hmem χ)
      (approximation_tendsto_orbit i τ hτ χ)

end CommonPositiveRealEdgeData

/-- The complete gluable Chapter V generator family reconstructed from
sourcewise locally uniform spatial-distribution approximants. -/
noncomputable def toGeneratorFamily
    (A : GeneratorSpatialApproximationFamily d k) :
    A.CommonPositiveRealEdgeData →
      (∀ i j, IsConnected (A.domain i ∩ A.domain j)) →
    GeneratorFamily d k :=
  fun E hoverlap =>
    GeneratorFamily.ofCommonPositiveRealEdge
      A.domain A.domain_open A.distribution A.distribution_weaklyHolomorphic
      E.orbit E.realRegion E.realRegion_open E.realRegion_nonempty
      (A.distribution_commonPositiveRealEdge E) hoverlap

/-- Build the gluable generator family directly when every generator domain
is convex. The common positive-real edge makes all pairwise overlaps
nonempty, so connectedness is automatic. -/
noncomputable def toGeneratorFamilyOfConvex
    (A : GeneratorSpatialApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData)
    (hconvex : ∀ i, Convex ℝ (A.domain i)) :
    GeneratorFamily d k :=
  A.toGeneratorFamily E
    (CommonPositiveRealEdgeData.overlap_connected_of_convex A E hconvex)

/-- The assembled generator family retains the declared common A0 real
orbit. -/
theorem toGeneratorFamily_hasCommonPositiveRealEdge
    (A : GeneratorSpatialApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData)
    (hoverlap : ∀ i j, IsConnected (A.domain i ∩ A.domain j)) :
    (A.toGeneratorFamily E hoverlap).HasCommonPositiveRealEdge
      E.orbit E.realRegion := by
  exact
    GeneratorFamily.ofCommonPositiveRealEdge_hasCommonPositiveRealEdge
      A.domain A.domain_open A.distribution
      A.distribution_weaklyHolomorphic
      E.orbit E.realRegion E.realRegion_open E.realRegion_nonempty
      (A.distribution_commonPositiveRealEdge E) hoverlap

/-- Once the existing A0 representation and pointwise-boundedness statements
are supplied, sourcewise spatial assembly produces the complete positive-real
edge package for the glued continuation stage. -/
noncomputable def toTimeContinuationStagePositiveRealEdgeData
    [NeZero d]
    (A : GeneratorSpatialApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData)
    (hoverlap : ∀ i j, IsConnected (A.domain i ∩ A.domain j))
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (i : GeneratorIndex k)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn
        W E.orbit E.realRegion)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        E.orbit E.realRegion) :
    (A.toGeneratorFamily E hoverlap).toTimeContinuationStage.PositiveRealEdgeData
      W E.realRegion :=
  (A.toGeneratorFamily E hoverlap
    ).toTimeContinuationStagePositiveRealEdgeData
    E.orbit E.realRegion W
    (A.toGeneratorFamily_hasCommonPositiveRealEdge E hoverlap)
    i hrep hbounded

/-- Convex generator domains eliminate the separate overlap-connectedness
input from the positive-real stage handoff. -/
noncomputable def toTimeContinuationStagePositiveRealEdgeDataOfConvex
    [NeZero d]
    (A : GeneratorSpatialApproximationFamily d k)
    (E : A.CommonPositiveRealEdgeData)
    (hconvex : ∀ i, Convex ℝ (A.domain i))
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (i : GeneratorIndex k)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn
        W E.orbit E.realRegion)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        E.orbit E.realRegion) :
    (A.toGeneratorFamilyOfConvex E hconvex
      ).toTimeContinuationStage.PositiveRealEdgeData
        W E.realRegion :=
  A.toTimeContinuationStagePositiveRealEdgeData E
    (CommonPositiveRealEdgeData.overlap_connected_of_convex A E hconvex)
    W i hrep hbounded

end GeneratorSpatialApproximationFamily

end OSIIChapterV
end OSReconstruction
