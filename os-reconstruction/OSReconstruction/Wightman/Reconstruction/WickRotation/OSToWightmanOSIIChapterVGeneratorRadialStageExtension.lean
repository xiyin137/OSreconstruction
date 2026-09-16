import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageConvexAtlas

/-!
# Radial generator extensions of Chapter V stages

The target-covering global generator domains are open and radially
contractible toward their common positive-real edge, but need not be convex.
This file packages the exact replacement for the older convex-generator
successor argument:

* radial generator overlaps are connected;
* the intersection of a radial generator with each convex predecessor chart
  is connected;
* totally-real uniqueness therefore gives agreement with the predecessor
  chart by chart and compatibility across all generator splits.

No convexity of the complete generator domains or of the predecessor carrier
is asserted.
-/

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace GeneratorSpatialApproximationFamily

variable {d k : ℕ} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d}

/-- Evaluation of a common positive-real orbit on a fixed spatial test is
continuous.  This follows from one holomorphic branch and the common-edge
identity. -/
theorem CommonPositiveRealEdgeData.orbit_continuousOn
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ContinuousOn (fun τ => E.orbit τ χ) E.realRegion := by
  let i₀ : GeneratorIndex k := GeneratorIndex.ofGap (0 : Fin k)
  have hhol :
      DifferentiableOn ℂ
        (fun z => B.scalarLimit i₀ z χ) (B.domain i₀) :=
    (B.locallyUniform i₀ χ).differentiableOn_finite
      (Filter.Eventually.of_forall fun N =>
        B.approximation_weaklyHolomorphic i₀ N χ)
      (B.domain_open i₀)
  have hcontinuous :
      ContinuousOn
        (fun τ =>
          B.scalarLimit i₀ (osiiPositiveRealTimeEmbed τ) χ)
        E.realRegion :=
    hhol.continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun τ hτ => (E.scalarLimit_realEdge i₀ τ hτ).1)
  exact
    hcontinuous.congr fun τ hτ =>
      ((E.scalarLimit_realEdge i₀ τ hτ).2 χ).symm

/-- Pairwise intersections of radial generator domains are connected because
the common positive-real edge supplies a point in every overlap. -/
theorem radialDomains_overlap_connected
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i) :
    ∀ i j, IsConnected (B.domain i ∩ B.domain j) := by
  intro i j
  obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
  have hi :
      osiiPositiveRealTimeEmbed τ ∈
        F.radialChronologicalDomain i := by
    rw [← domain_eq i]
    exact (B.distribution_commonPositiveRealEdge E i τ hτ).1
  have hj :
      osiiPositiveRealTimeEmbed τ ∈
        F.radialChronologicalDomain j := by
    rw [← domain_eq j]
    exact (B.distribution_commonPositiveRealEdge E j τ hτ).1
  rw [domain_eq i, domain_eq j]
  exact
    (F.radialChronologicalDomain_inter_isPathConnected
      F i j hi hj).isConnected

/-- Compare a radial generator with an old continuation stage chart by chart.

The common real region is required to be closed under positive contractions.
This keeps the radial segment through the chosen common edge point inside
every predecessor convex chart. -/
theorem agreesOnOld_of_radialConvexAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas A E.realRegion ι)
    (real_smul_mem :
      ∀ τ, τ ∈ E.realRegion → ∀ {t : ℝ},
        0 < t → t ≤ 1 → t • τ ∈ E.realRegion) :
    ∀ i, Set.EqOn (B.distribution i) A.distribution
      (B.domain i ∩ A.carrier) := by
  intro i z hz
  obtain ⟨j, hj⟩ :=
    Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hz.2)
  apply ContinuousLinearMap.ext
  intro χ
  let D : Set (OSIITimeGapSpace k) :=
    B.domain i ∩ atlas.domain j
  let G : OSIITimeGapSpace k → ℂ :=
    fun w => B.distribution i w χ - A.distribution w χ
  have hD_open : IsOpen D :=
    (B.domain_open i).inter (atlas.domain_open j)
  obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
  have hcF :
      osiiPositiveRealTimeEmbed τ ∈
        F.radialChronologicalDomain i := by
    rw [← domain_eq i]
    exact (B.distribution_commonPositiveRealEdge E i τ hτ).1
  have hcAtlas :
      osiiPositiveRealTimeEmbed τ ∈ atlas.domain j :=
    atlas.realEdge_mem j τ hτ
  have hradialAtlas :
      IsPathConnected
        (F.radialChronologicalDomain i ∩ atlas.domain j) := by
    apply F.radialChronologicalDomain_inter_convex_isPathConnected
      i (atlas.domain_convex j) hcF hcAtlas
    intro t ht0 ht1
    have htτ : t • τ ∈ E.realRegion :=
      real_smul_mem τ hτ ht0 ht1
    have hscale :
        t • osiiPositiveRealTimeEmbed τ =
          osiiPositiveRealTimeEmbed (t • τ) := by
      ext q
      simp [osiiPositiveRealTimeEmbed]
    rw [hscale]
    exact atlas.realEdge_mem j (t • τ) htτ
  have hD_connected : IsConnected D := by
    simpa [D, domain_eq i] using hradialAtlas.isConnected
  have hG : DifferentiableOn ℂ G D :=
    ((B.distribution_weaklyHolomorphic i χ).mono
      Set.inter_subset_left).sub
      ((A.weaklyHolomorphic χ).mono
        (Set.inter_subset_right.trans
          (atlas.domain_subset_carrier j)))
  have hU_sub :
      ∀ u ∈ E.realRegion, SCV.realToComplex u ∈ D := by
    intro u hu
    have hnew :=
      (B.distribution_commonPositiveRealEdge E i u hu).1
    have hold_chart := atlas.realEdge_mem j u hu
    change SCV.realToComplex u ∈ B.domain i ∩ atlas.domain j
    rw [show SCV.realToComplex u =
        osiiPositiveRealTimeEmbed u by rfl]
    exact ⟨hnew, hold_chart⟩
  have hG_zero :
      ∀ u ∈ E.realRegion, G (SCV.realToComplex u) = 0 := by
    intro u hu
    have hnew :=
      (B.distribution_commonPositiveRealEdge E i u hu).2
    have hold_eq := (hold u hu).2
    simp only [G]
    rw [show SCV.realToComplex u =
        osiiPositiveRealTimeEmbed u by rfl,
      hnew, hold_eq, sub_self]
  have hzD : z ∈ D := ⟨hz.1, hj⟩
  have hz_zero :
      G z = 0 :=
    SCV.identity_theorem_totally_real
      hD_open hD_connected hG
      E.realRegion_open E.realRegion_nonempty
      hU_sub hG_zero z hzD
  exact sub_eq_zero.mp hz_zero

/-- Radial generator domains extend a stage carrying a convex common-edge
atlas.  Convexity is used only for the predecessor charts, never for the
complete new generator domains. -/
noncomputable def toStageExtensionDataOfRadialConvexAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas A E.realRegion ι)
    (real_smul_mem :
      ∀ τ, τ ∈ E.realRegion → ∀ {t : ℝ},
        0 < t → t ≤ 1 → t • τ ∈ E.realRegion) :
    GeneratorStageExtensionData A := by
  let agrees :
      ∀ i, Set.EqOn (B.distribution i) A.distribution
        (B.domain i ∩ A.carrier) :=
    B.agreesOnOld_of_radialConvexAtlas
      E F domain_eq A hold atlas real_smul_mem
  exact
    { domain := B.domain
      domain_open := B.domain_open
      distribution := B.distribution
      weaklyHolomorphic := B.distribution_weaklyHolomorphic
      compatible :=
        GeneratorStageExtensionData.compatible_of_agreesOnOld
          B.domain B.domain_open B.distribution
          B.distribution_weaklyHolomorphic
          (B.radialDomains_overlap_connected E F domain_eq)
          (by
            intro i j
            obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
            exact
              ⟨osiiPositiveRealTimeEmbed τ,
                ⟨⟨(B.distribution_commonPositiveRealEdge E i τ hτ).1,
                    (B.distribution_commonPositiveRealEdge E j τ hτ).1⟩,
                  (hold τ hτ).1⟩⟩)
          agrees
      agreesOnOld := agrees }

@[simp]
theorem toStageExtensionDataOfRadialConvexAtlas_domain
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (F : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (domain_eq :
      ∀ i, B.domain i = F.radialChronologicalDomain i)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas A E.realRegion ι)
    (real_smul_mem :
      ∀ τ, τ ∈ E.realRegion → ∀ {t : ℝ},
        0 < t → t ≤ 1 → t • τ ∈ E.realRegion)
    (i : GeneratorIndex k) :
    (B.toStageExtensionDataOfRadialConvexAtlas
      E F domain_eq A hold atlas real_smul_mem).domain i =
      B.domain i :=
  rfl

end GeneratorSpatialApproximationFamily

end OSIIChapterV
end OSReconstruction
