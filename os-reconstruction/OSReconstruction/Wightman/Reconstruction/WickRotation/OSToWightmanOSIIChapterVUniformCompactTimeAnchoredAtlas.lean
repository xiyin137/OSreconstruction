/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedAnchoredAtlas















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q N : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) → ℝ)}

abbrev AnchoredSourceIndex
    (d q : ℕ) [NeZero d]
    (K : Set (Fin ((q + 1) + 1) → ℝ)) :=
  UniformCompactTimeSource d ((q + 1) + 1) K

def anchoredAtlasCoveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    Set (Fin (q + 1) → ℂ) :=
  SourceIndexedAnchoredReflectedGramChart.coveredDomain
    (H := OSHilbertSpace OS)
    (ι := AnchoredSourceIndex d q K)
    (m := q + 1)
    (scalar := fun a b => (G.cauchy a b).scalar)
    (anchorPoint := (0 : Fin (q + 1) → ℂ))
    (anchorField := fun a => G.hilbert.field a 0)

/-- The quantitative atlas union consisting only of charts reached by finite
Cauchy continuation chains from the concrete initial Gram seed. -/
def reachableAnchoredAtlasCoveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    Set (Fin (q + 1) → ℂ) :=
  SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain
    (H := OSHilbertSpace OS)
    (iota := AnchoredSourceIndex d q K)
    (k := q)
    (scalar := fun a b => (G.cauchy a b).scalar)
    (anchorPoint := (0 : Fin (q + 1) → ℂ))
    (anchorField := fun a => G.hilbert.field a 0)
    (P := G.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)

def anchoredAtlasField
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    (Fin (q + 1) → ℂ) → OSHilbertSpace OS :=
  SourceIndexedAnchoredReflectedGramChart.gluedField
    (H := OSHilbertSpace OS)
    (scalar := fun a b => (G.cauchy a b).scalar)
    (anchorPoint := (0 : Fin (q + 1) → ℂ))
    (anchorField := fun a => G.hilbert.field a 0)
    a

/-- At one fixed source, the production anchored charts form the directly
compatible atlas consumed by the stage-wide mixed-domain package. -/
def anchoredCompatibleHilbertFieldAtlas
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    CompatibleHilbertFieldAtlas (OSHilbertSpace OS) (q + 1)
      (SourceIndexedAnchoredReflectedGramChart
        (OSHilbertSpace OS) (AnchoredSourceIndex d q K) (q + 1)
        (fun a b => (G.cauchy a b).scalar)
        (0 : Fin (q + 1) → ℂ)
        (fun a => G.hilbert.field a 0)) :=
  SourceIndexedAnchoredReflectedGramChart.toCompatibleHilbertFieldAtlas
    (H := OSHilbertSpace OS)
    (scalar := fun a b => (G.cauchy a b).scalar)
    (anchorPoint := (0 : Fin (q + 1) → ℂ))
    (anchorField := fun a => G.hilbert.field a 0)
    a

@[simp]
theorem anchoredCompatibleHilbertFieldAtlas_coveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    (G.anchoredCompatibleHilbertFieldAtlas stage germ a).coveredDomain =
      G.anchoredAtlasCoveredDomain stage germ :=
  rfl

@[simp]
theorem anchoredCompatibleHilbertFieldAtlas_gluedField
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    (G.anchoredCompatibleHilbertFieldAtlas stage germ a).gluedField =
      G.anchoredAtlasField stage germ a :=
  rfl

theorem anchoredAtlasCoveredDomain_open
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    IsOpen (G.anchoredAtlasCoveredDomain stage germ) :=
  SourceIndexedAnchoredReflectedGramChart.coveredDomain_open

theorem reachableAnchoredAtlasCoveredDomain_open
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    IsOpen (G.reachableAnchoredAtlasCoveredDomain stage germ) :=
  SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain_open

/-- The reachable atlas is the provenance-carrying quantitative subatlas of
the maximal qualitative atlas used for global gluing. -/
theorem reachableAnchoredAtlasCoveredDomain_subset_anchoredAtlasCoveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    G.reachableAnchoredAtlasCoveredDomain stage germ ⊆
      G.anchoredAtlasCoveredDomain stage germ :=
  SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain_subset_maximal

theorem anchoredAtlasField_holomorphic
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    DifferentiableOn ℂ (G.anchoredAtlasField stage germ a)
      (G.anchoredAtlasCoveredDomain stage germ) :=
  SourceIndexedAnchoredReflectedGramChart.gluedField_holomorphic a

theorem anchoredAtlas_scalar_eq_inner_anchor
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a b : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ) :
    (G.cauchy a b).scalar
        (reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z) =
      @inner ℂ (OSHilbertSpace OS) _
        (G.hilbert.field a 0)
        (G.anchoredAtlasField stage germ b z) :=
  SourceIndexedAnchoredReflectedGramChart.scalar_eq_inner_anchor_gluedField
    a b z hz

theorem anchoredAtlasField_mem_sourceAnchorSpan
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ G.anchoredAtlasCoveredDomain stage germ) :
    G.anchoredAtlasField stage germ a z ∈
      sourceAnchorSpan (fun b => G.hilbert.field b 0) :=
  SourceIndexedAnchoredReflectedGramChart.gluedField_mem_sourceAnchorSpan
    a z hz

theorem generatedMixedCarrier_subset_anchoredAtlasCoveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) N) ⊆
        stage.carrier) :
    osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase ((q + 1) + 1) N) ⊆
      G.anchoredAtlasCoveredDomain stage germ := by
  let P :=
    G.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ
  let A₀ :=
    G.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      stage germ
  exact
    OSIIChapterV.generatedMixedCarrier_subset_anchoredAtlasCoveredDomain
      P A₀ stage germ.η germ.η_support hgenerated rfl
      (SCV.center_mem_polydisc fun _ => G.gramRadius_pos)

theorem anchoredAtlasField_eq_initial
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => G.gramRadius)) :
    G.anchoredAtlasField stage germ a z =
      G.hilbert.field a z := by
  let P :=
    G.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ
  let A₀ :=
    G.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      stage germ
  let C :
      SourceIndexedAnchoredReflectedGramChart
        (OSHilbertSpace OS) (AnchoredSourceIndex d q K) (q + 1)
        (fun a b => (G.cauchy a b).scalar)
        (0 : Fin (q + 1) → ℂ)
        (fun a => G.hilbert.field a 0) :=
    { gram := P, anchored := A₀ }
  exact
    SourceIndexedAnchoredReflectedGramChart.gluedField_eqOn_domain
      C a hz

def anchoredAtlasRealRegion
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    Set (Fin (q + 1) → ℝ) :=
  G.hilbert.realRegion ∩
    SCV.realToComplex ⁻¹'
      SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => G.gramRadius)

theorem anchoredAtlasRealRegion_open
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    IsOpen (G.anchoredAtlasRealRegion stage germ) := by
  have hrealToComplex :
      Continuous
        (SCV.realToComplex :
          (Fin (q + 1) → ℝ) → Fin (q + 1) → ℂ) :=
    continuous_pi fun i =>
      Complex.continuous_ofReal.comp (continuous_apply i)
  exact
    G.hilbert.realRegion_open.inter
      (SCV.polydisc_isOpen.preimage hrealToComplex)

theorem anchoredAtlasRealRegion_mem_nhds
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ) :
    G.anchoredAtlasRealRegion stage germ ∈
      𝓝 (0 : Fin (q + 1) → ℝ) := by
  apply (G.anchoredAtlasRealRegion_open stage germ).mem_nhds
  constructor
  · exact mem_of_mem_nhds G.hilbert.realRegion_nhds
  · change
      (0 : Fin (q + 1) → ℂ) ∈
        SCV.Polydisc
          (0 : Fin (q + 1) → ℂ) (fun _ => G.gramRadius)
    exact SCV.center_mem_polydisc fun _ => G.gramRadius_pos

theorem anchoredAtlasField_realEdge
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (a : AnchoredSourceIndex d q K) :
    HasPositiveTimeSourceRealEdge OS
      (G.anchoredAtlasField stage germ a)
      (localPositiveTimeParameterTranslate
        (UniformCompactTimeSource.source (K := K) a)
        (fun r : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) r))
      (G.anchoredAtlasRealRegion stage germ) := by
  intro x hx
  change
    G.anchoredAtlasField stage germ a (SCV.realToComplex x) =
      osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
        (localPositiveTimeParameterTranslate
          (UniformCompactTimeSource.source (K := K) a)
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r) x)
  rw [G.anchoredAtlasField_eq_initial stage germ a
    (SCV.realToComplex x) hx.2]
  exact G.hilbert.realEdge a x hx.1

end UniformCompactTimeMixedHilbertGramFamilyData
end OSIIChapterV
end OSReconstruction
