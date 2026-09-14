import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedGram

/-!
# Canonical reduced-cutoff predecessor bridge

A Chapter V predecessor stage carries one fixed reduced A0 extension.  A new
mixed source family generally chooses a different auxiliary cutoff, so the
predecessor should not be required to represent that auxiliary distribution
on every Schwartz test.

This file records the exact source-level comparison.  The predecessor's fixed
canonical reduced cutoff only has to fix the concrete translated mixed
sources.  Cutoff recovery and chronological reindexing then give the intended
Schwinger values, after which the existing moving-slice currying theorem
constructs the stage-orbit edge.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- A mixed source family compared with the fixed canonical reduced A0
extension represented by a predecessor stage.

The remaining eventual field is the genuine support obligation: the
predecessor's reduced-time cutoff is one on the chronologically reordered
translated source support.

The zero-diagonal property of the raw translated products is derived from the
uniform compact strict-positive support witness.  No equality of full
auxiliary distributions is assumed. -/
structure UniformCompactTimeMixedCanonicalCutoffStageData
    {q : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2)) where
  uniformSupport :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun a => (f a).1)
  germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f
  stageCutoff :
    SchwartzMap (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ
  stageCutoff_support :
    tsupport
        (stageCutoff :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion
        ((q + 1) + ((q + 1) + 1))
  stage : OSIITimeContinuationStage d
    ((q + 1) + ((q + 1) + 1))
  realRegion : Set (Fin ((q + 1) + ((q + 1) + 1)) → ℝ)
  realRegion_open : IsOpen realRegion
  cutoff_support :
    tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ) ⊆
      realRegion
  edge :
    stage.PositiveRealEdgeData
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS stageCutoff stageCutoff_support))
      realRegion
  stageCutoff_one_on :
    ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
      ∀ ab : ι × ι,
        ∀ x ∈ tsupport
            (translateSchwartzConfiguration
              (reflectedReducedAbsoluteDisplacement (d := d) u)
              (mixedReflectedChronologicalSource
                (f ab.1).1 (f ab.2).1) :
              NPointDomain d
                (((q + 1) + ((q + 1) + 1)) + 1) → ℂ),
          reducedTimeCutoffWeight (d := d) stageCutoff x = 1

namespace UniformCompactTimeMixedReflectedSourceStageData

/-- A represented mixed stage already carries all data needed by the
canonical-cutoff bridge. The germ constructor retains both the canonical
identity of its reduced distribution and the support-one neighborhood used
to construct that cutoff. -/
noncomputable def toCanonicalCutoffStageData
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (uniformSupport :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (S : UniformCompactTimeMixedReflectedSourceStageData OS f) :
    UniformCompactTimeMixedCanonicalCutoffStageData OS f where
  uniformSupport := uniformSupport
  germ := S.germ
  stageCutoff := S.germ.η
  stageCutoff_support := S.germ.η_support
  stage := S.stage
  realRegion := S.realRegion
  realRegion_open := S.realRegion_open
  cutoff_support := S.cutoff_support
  edge := by
    simpa [S.germ.W_eq_canonical] using S.edge
  stageCutoff_one_on := S.germ.cutoff_one_on

end UniformCompactTimeMixedReflectedSourceStageData

namespace UniformCompactTimeMixedCanonicalCutoffStageData

/-- The fixed canonical predecessor cutoff gives the source-specific ordered
current edge required by the mixed moving-slice construction. -/
noncomputable def toOrderedSourceStageData
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (S : UniformCompactTimeMixedCanonicalCutoffStageData OS f) :
    UniformCompactTimeMixedOrderedSourceStageData OS f where
  germ := S.germ
  stage := S.stage
  representedDistribution :=
    orderedTransportDistribution
      (canonicalReducedTimeCutoffSchwingerCLM
        OS S.stageCutoff S.stageCutoff_support)
  realRegion := S.realRegion
  realRegion_open := S.realRegion_open
  cutoff_support := S.cutoff_support
  edge := S.edge
  orderedSourceEdge := by
    let F :
        ι × ι →
          SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
      fun ab =>
        diffVarReduction d ((q + 1) + ((q + 1) + 1))
          (mixedReflectedChronologicalSource
            (f ab.1).1 (f ab.2).1)
    let raw :
        ι × ι → (Fin ((q + 1) + (q + 1)) → ℝ) → ℂ :=
      fun ab u =>
        OS.S ((q + 2) + (q + 2))
          (ZeroDiagonalSchwartz.ofClassical
            (translateSchwartzConfiguration
              (reflectedSourceParameterDisplacementCLM
                (fun r : Fin (q + 1) =>
                  chronologicalTimeSourceDirection (d := d) r) u)
              ((f ab.1).1.osConjTensorProduct (f ab.2).1)))
    have hcutoff :
        ∀ ab,
          SchwartzMap.smulLeftCLM ℂ
              (section43NPointTimeCutoffWeight d
                ((q + 1) + ((q + 1) + 1)) S.germ.η)
              (F ab) =
            F ab := by
      intro ab
      simpa [F] using S.germ.cutoff ab.1 ab.2
    have hedge :
        ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
          ∀ ab,
            canonicalReducedTimeCutoffSchwingerCLM
                OS S.stageCutoff S.stageCutoff_support
                (translateSchwartzConfiguration
                  (osiiDifferenceTimeTranslation (d := d)
                    (reflectedReducedTimeDisplacement u))
                  (F ab)) =
              raw ab u := by
      filter_upwards [
        eventually_mixedReflectedRawTranslation_vanishes_of_uniformCompactTimeSupport
          f S.uniformSupport,
        S.stageCutoff_one_on] with
        u hraw hone
      intro ab
      let ψ :
          SchwartzNPoint d
            (((q + 1) + ((q + 1) + 1)) + 1) :=
        translateSchwartzConfiguration
          (reflectedReducedAbsoluteDisplacement (d := d) u)
          (mixedReflectedChronologicalSource
            (f ab.1).1 (f ab.2).1)
      have hψ :
          VanishesToInfiniteOrderOnCoincidence ψ := by
        exact
          translate_mixedReflectedChronologicalSource_vanishes_of_raw
            u (f ab.1).1 (f ab.2).1 (hraw ab)
      calc
        canonicalReducedTimeCutoffSchwingerCLM
            OS S.stageCutoff S.stageCutoff_support
            (translateSchwartzConfiguration
              (osiiDifferenceTimeTranslation (d := d)
                (reflectedReducedTimeDisplacement u))
              (F ab)) =
          canonicalReducedTimeCutoffSchwingerCLM
            OS S.stageCutoff S.stageCutoff_support
            (diffVarReduction d
              ((q + 1) + ((q + 1) + 1)) ψ) := by
                rw [
                  translate_diffVarReduction_reflectedReducedTimeDisplacement]
        _ = OS.S (((q + 1) + ((q + 1) + 1)) + 1) ⟨ψ, hψ⟩ := by
          exact
            canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
              OS S.stageCutoff S.stageCutoff_support ψ hψ
                (reducedTimeCutoff_smul_eq_of_one_on_tsupport
                  S.stageCutoff ψ (by simpa [ψ] using hone ab))
        _ = raw ab u := by
          rw [← ZeroDiagonalSchwartz.ofClassical_of_vanishes ψ hψ]
          simpa [ψ, raw] using
            mixedReflectedChronologicalSource_schwinger_eq_raw
              OS u (f ab.1).1 (f ab.2).1 (hraw ab)
    simpa [F, raw] using
      orderedTransportDistribution_family_orderedSourceEdge_eventually
        S.germ.η
        (canonicalReducedTimeCutoffSchwingerCLM
          OS S.stageCutoff S.stageCutoff_support)
        F hcutoff raw hedge

/-- Consequently the predecessor's own positive-real orbit has the exact
mixed source integral edge consumed by the non-circular Hilbert-Gram
constructor. -/
noncomputable def toStageOrbitSourceData
    {q : ℕ} {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (S : UniformCompactTimeMixedCanonicalCutoffStageData OS f) :
    UniformCompactTimeMixedStageOrbitSourceData OS f :=
  (S.toOrderedSourceStageData OS f).toStageOrbitSourceData OS f

end UniformCompactTimeMixedCanonicalCutoffStageData

end OSIIChapterV
end OSReconstruction
