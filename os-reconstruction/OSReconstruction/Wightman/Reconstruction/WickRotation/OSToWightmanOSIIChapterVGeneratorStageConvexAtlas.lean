/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge


















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- An open convex chart cover of a continuation stage, with one positive-real
region lying in every chart.

The stage distribution itself is used on each chart.  No duplicate family of
local distributions is stored. -/
structure GeneratorStageConvexAtlas
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (realRegion : Set (Fin k → ℝ))
    (ι : Type*) where
  domain : ι → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  domain_convex : ∀ i, Convex ℝ (domain i)
  domain_subset_carrier : ∀ i, domain i ⊆ A.carrier
  carrier_subset_iUnion : A.carrier ⊆ ⋃ i, domain i
  realEdge_mem :
    ∀ i τ, τ ∈ realRegion →
      osiiPositiveRealTimeEmbed τ ∈ domain i

namespace GeneratorStageConvexAtlas

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}
  {U V : Set (Fin k → ℝ)}
  {ι : Type*}

/-- A convex stage carrier is the one-chart base case of the atlas
invariant. -/
def ofConvex
    (hold : A.HasPositiveRealEdge R U)
    (carrier_convex : Convex ℝ A.carrier) :
    GeneratorStageConvexAtlas A U PUnit where
  domain := fun _ => A.carrier
  domain_open := fun _ => A.carrier_open
  domain_convex := fun _ => carrier_convex
  domain_subset_carrier := fun _ => Set.Subset.rfl
  carrier_subset_iUnion := by
    intro z hz
    exact Set.mem_iUnion_of_mem PUnit.unit hz
  realEdge_mem := fun _ τ hτ => (hold τ hτ).1

/-- Shrink the declared common real edge without changing the complex chart
cover. -/
def restrictRealRegion
    (P : GeneratorStageConvexAtlas A U ι)
    (hVU : V ⊆ U) :
    GeneratorStageConvexAtlas A V ι where
  domain := P.domain
  domain_open := P.domain_open
  domain_convex := P.domain_convex
  domain_subset_carrier := P.domain_subset_carrier
  carrier_subset_iUnion := P.carrier_subset_iUnion
  realEdge_mem := fun i τ hτ => P.realEdge_mem i τ (hVU hτ)

/-- Recenter every atlas chart together with its common real edge. -/
def recenter
    (P : GeneratorStageConvexAtlas A U ι)
    (center : Fin k → ℝ) :
    GeneratorStageConvexAtlas
      (A.recenter center)
      {τ | τ + center ∈ U}
      ι where
  domain := fun i =>
    {z | z + osiiPositiveRealTimeEmbed center ∈ P.domain i}
  domain_open := fun i =>
    (P.domain_open i).preimage
      (continuous_id.add continuous_const)
  domain_convex := fun i =>
    (P.domain_convex i).translate_preimage_left
      (osiiPositiveRealTimeEmbed center)
  domain_subset_carrier := by
    intro i z hz
    exact P.domain_subset_carrier i hz
  carrier_subset_iUnion := by
    intro z hz
    obtain ⟨i, hi⟩ :=
      Set.mem_iUnion.mp (P.carrier_subset_iUnion hz)
    exact Set.mem_iUnion_of_mem i hi
  realEdge_mem := by
    intro i τ hτ
    simpa [osiiPositiveRealTimeEmbed_add] using
      P.realEdge_mem i (τ + center) hτ

end GeneratorStageConvexAtlas

namespace GeneratorSpatialApproximationFamily

variable {d k : ℕ}

/-- Compare a new generator with an old continuation stage chart by chart.

Every chart intersection is convex and contains the common positive-real
region.  Totally-real uniqueness gives agreement there; the atlas cover then
gives agreement on the new generator's full intersection with the old
carrier, without requiring that intersection itself to be connected. -/
theorem agreesOnOld_of_convexAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas A E.realRegion ι)
    (domain_convex : ∀ i, Convex ℝ (B.domain i)) :
    ∀ i, Set.EqOn (B.distribution i) A.distribution
      (B.domain i ∩ A.carrier) := by
  intro i z hz
  obtain ⟨j, hj⟩ :=
    Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hz.2)
  apply ContinuousLinearMap.ext
  intro χ
  let D : Set (OSIITimeGapSpace k) :=
    B.domain i ∩ atlas.domain j
  let F : OSIITimeGapSpace k → ℂ :=
    fun w => B.distribution i w χ - A.distribution w χ
  have hD_open : IsOpen D :=
    (B.domain_open i).inter (atlas.domain_open j)
  have hD_connected : IsConnected D := by
    apply ((domain_convex i).inter (atlas.domain_convex j)).isConnected
    obtain ⟨τ, hτ⟩ := E.realRegion_nonempty
    exact
      ⟨osiiPositiveRealTimeEmbed τ,
        (B.distribution_commonPositiveRealEdge E i τ hτ).1,
        atlas.realEdge_mem j τ hτ⟩
  have hF : DifferentiableOn ℂ F D :=
    ((B.distribution_weaklyHolomorphic i χ).mono
      Set.inter_subset_left).sub
      ((A.weaklyHolomorphic χ).mono
        (Set.inter_subset_right.trans
          (atlas.domain_subset_carrier j)))
  have hU_sub :
      ∀ τ ∈ E.realRegion, SCV.realToComplex τ ∈ D := by
    intro τ hτ
    have hnew :=
      (B.distribution_commonPositiveRealEdge E i τ hτ).1
    have hold_chart := atlas.realEdge_mem j τ hτ
    simpa [D, SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      (show osiiPositiveRealTimeEmbed τ ∈
          B.domain i ∩ atlas.domain j from
        ⟨hnew, hold_chart⟩)
  have hF_zero :
      ∀ τ ∈ E.realRegion, F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    have hnew :=
      (B.distribution_commonPositiveRealEdge E i τ hτ).2
    have hold_eq := (hold τ hτ).2
    simp only [F]
    rw [show SCV.realToComplex τ =
        osiiPositiveRealTimeEmbed τ by rfl,
      hnew, hold_eq, sub_self]
  have hzD : z ∈ D := ⟨hz.1, hj⟩
  have hz_zero :
      F z = 0 :=
    SCV.identity_theorem_totally_real
      hD_open hD_connected hF
      E.realRegion_open E.realRegion_nonempty
      hU_sub hF_zero z hzD
  exact sub_eq_zero.mp hz_zero

/-- Convex generator domains extend a stage carrying a convex common-edge
atlas.  This is the branchwise replacement for connectedness of the
intersection with the whole old carrier. -/
noncomputable def toStageExtensionDataOfConvexAtlas
    (B : GeneratorSpatialApproximationFamily d k)
    (E : B.CommonPositiveRealEdgeData)
    (A : OSIITimeContinuationStage d k)
    (hold : A.HasPositiveRealEdge E.orbit E.realRegion)
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas A E.realRegion ι)
    (domain_convex : ∀ i, Convex ℝ (B.domain i)) :
    GeneratorStageExtensionData A where
  domain := B.domain
  domain_open := B.domain_open
  distribution := B.distribution
  weaklyHolomorphic := B.distribution_weaklyHolomorphic
  compatible :=
    (B.toGeneratorFamilyOfConvex E domain_convex).compatible
  agreesOnOld :=
    B.agreesOnOld_of_convexAtlas E A hold atlas domain_convex

end GeneratorSpatialApproximationFamily

namespace GeneratorStageExtensionData

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}
  {U : Set (Fin k → ℝ)}
  {ι : Type*}

/-- The old convex charts and the newly adjoined convex generator domains
form a convex atlas for the successor stage. -/
def toConvexAtlas
    (C : GeneratorStageExtensionData A)
    (atlas : GeneratorStageConvexAtlas A U ι)
    (domain_convex : ∀ i, Convex ℝ (C.domain i))
    (newEdge_mem :
      ∀ i τ, τ ∈ U →
        osiiPositiveRealTimeEmbed τ ∈ C.domain i) :
    GeneratorStageConvexAtlas
      C.toTimeContinuationStage U (Sum ι (GeneratorIndex k)) where
  domain
    | Sum.inl i => atlas.domain i
    | Sum.inr i => C.domain i
  domain_open
    | Sum.inl i => atlas.domain_open i
    | Sum.inr i => C.domain_open i
  domain_convex
    | Sum.inl i => atlas.domain_convex i
    | Sum.inr i => domain_convex i
  domain_subset_carrier := by
    intro p z hz
    cases p with
    | inl i =>
        exact C.oldCarrier_subset_newCarrier
          (atlas.domain_subset_carrier i hz)
    | inr i =>
        exact Set.mem_iUnion_of_mem (some i) hz
  carrier_subset_iUnion := by
    intro z hz
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
    cases p with
    | none =>
        obtain ⟨i, hi⟩ :=
          Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hp)
        exact Set.mem_iUnion_of_mem (Sum.inl i) hi
    | some i =>
        exact Set.mem_iUnion_of_mem (Sum.inr i) hp
  realEdge_mem := by
    intro p τ hτ
    cases p with
    | inl i => exact atlas.realEdge_mem i τ hτ
    | inr i => exact newEdge_mem i τ hτ

end GeneratorStageExtensionData

end OSIIChapterV
end OSReconstruction
