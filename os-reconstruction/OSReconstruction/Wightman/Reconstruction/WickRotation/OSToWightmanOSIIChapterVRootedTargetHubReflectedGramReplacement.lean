/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- A stage-wide reflected-Gram package adapted to one physical target and
one positive-real hub in both rooted blocks of a generator split. -/
structure RootedTargetHubAdaptedReflectedGramData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (z : OSIITimeGapSpace k) where
  adapted : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth
  left_segment :
    segment ℝ
        (rootedLeftBlockTarget i
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor))
        (rootedLeftBlockTarget i
          (z - osiiPositiveRealTimeEmbed anchor)) ⊆
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth adapted A R H).radialLeftDomain i
  right_segment :
    segment ℝ
        (rootedRightBlockTarget i
          (osiiPositiveRealTimeEmbed hub -
            osiiPositiveRealTimeEmbed anchor))
        (rootedRightBlockTarget i
          (z - osiiPositiveRealTimeEmbed anchor)) ⊆
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth adapted A R H).radialRightDomain i

namespace RootedTargetHubAdaptedReflectedGramData

variable
  {S : C}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {H : RootedA0BlockContinuousTranslationData OS A R}
  {i : GeneratorIndex k}
  {hub : Fin k → ℝ}
  {z : OSIITimeGapSpace k}

/-- The two adapted block segments assemble into the physical centered global
hub-to-target segment in the rooted radial chronological domain. -/
theorem centeredHub_target_segment_subset_radialChronologicalDomain
    (D :
      RootedTargetHubAdaptedReflectedGramData
        S depth P A R H i hub z)
    (hbridge_hub :
      anchor i.bridgeGlobalIndex < hub i.bridgeGlobalIndex)
    (hbridge_target :
      anchor i.bridgeGlobalIndex <
        (z i.bridgeGlobalIndex).re) :
    segment ℝ
        (osiiPositiveRealTimeEmbed hub -
          osiiPositiveRealTimeEmbed anchor)
        (z - osiiPositiveRealTimeEmbed anchor) ⊆
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth D.adapted A R H).radialChronologicalDomain i :=
  OSReconstruction.OSIIChapterV.Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData.centeredHub_target_segment_subset_radialChronologicalDomain
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth D.adapted A R H)
      i hub anchor z hbridge_hub hbridge_target
      D.left_segment D.right_segment

end RootedTargetHubAdaptedReflectedGramData

/-- Every subset of a one-particle left block lies in its radial domain,
because the centered block coordinate space is zero-dimensional. -/
theorem subset_radialLeftDomain_of_arity_one
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (hi : i.n = 1)
    (U : Set (Fin (i.n - 1) → ℂ)) :
    U ⊆ E.radialLeftDomain i := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst n
  intro z hz
  have hz0 : z = 0 := by
    funext a
    exact Fin.elim0 (show Fin 0 from by simpa using a)
  rw [hz0]
  exact E.zero_mem_radialLeftDomain
    ⟨1, m, hn, hm, hnm⟩

/-- Right-hand form of `subset_radialLeftDomain_of_arity_one`. -/
theorem subset_radialRightDomain_of_arity_one
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (hi : i.m = 1)
    (U : Set (Fin (i.m - 1) → ℂ)) :
    U ⊆ E.radialRightDomain i := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst m
  intro z hz
  have hz0 : z = 0 := by
    funext a
    exact Fin.elim0 (show Fin 0 from by simpa using a)
  rw [hz0]
  exact E.zero_mem_radialRightDomain
    ⟨n, 1, hn, hm, hnm⟩

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
