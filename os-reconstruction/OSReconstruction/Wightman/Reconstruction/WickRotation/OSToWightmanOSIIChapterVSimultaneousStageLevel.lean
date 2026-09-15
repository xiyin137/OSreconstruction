/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

namespace OSIITimeContinuationStage
namespace PositiveRealEdgeData

variable {d k : ℕ} [NeZero d]
  {A : OSIITimeContinuationStage d k}
  {W : SchwartzNPoint d k →L[ℂ] ℂ}
  {U : Set (Fin k → ℝ)}

/-- Reuse an existing stage orbit on a smaller real region for another
spacetime distribution once that distribution is represented by the same
orbit there.  Stage agreement and pointwise boundedness are inherited. -/
noncomputable def changeDistributionOnSubset
    (E : A.PositiveRealEdgeData W U)
    (W' : SchwartzNPoint d k →L[ℂ] ℂ)
    (V : Set (Fin k → ℝ))
    (hVU : V ⊆ U)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn W' E.orbit V) :
    A.PositiveRealEdgeData W' V where
  orbit := E.orbit
  stageEdge := fun τ hτ => E.stageEdge τ (hVU hτ)
  represents := hrep
  pointwiseBounded := by
      intro χ
      obtain ⟨C, hC⟩ := E.pointwiseBounded χ
      exact ⟨C, fun τ hτ => hC τ (hVU hτ)⟩

/-- Restrict a positive-real edge to a smaller real region without changing
its represented distribution or orbit. -/
noncomputable def restrictRegion
    (E : A.PositiveRealEdgeData W U)
    (V : Set (Fin k → ℝ))
    (hVU : V ⊆ U) :
    A.PositiveRealEdgeData W V :=
  E.changeDistributionOnSubset W V hVU (by
    intro χ
    exact
      SCV.representsDistributionOn_congr_on_subset
        (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
        (E.represents χ) (fun _ _ => rfl) hVU)

end PositiveRealEdgeData
end OSIITimeContinuationStage

namespace OSIIChapterV

/-- One fixed Chapter V induction level, with a continuation stage at every
reduced time-gap arity.  Compatibility between successive induction levels is
a separate obligation. -/
structure SimultaneousTimeContinuationStageLevel (d : ℕ) where
  stage : (k : ℕ) → OSIITimeContinuationStage d k

namespace SimultaneousTimeContinuationStageLevel

variable {d q : ℕ}

/-- Assemble a simultaneous level from positive-arity stages.  The
zero-gap stage is inserted canonically because it carries no analytic
continuation obligation. -/
noncomputable def ofPositiveArityStages
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (positiveStage :
      (k : ℕ) → OSIITimeContinuationStage d (k + 1)) :
    SimultaneousTimeContinuationStageLevel d where
  stage
    | 0 => canonicalZeroGapTimeContinuationStage OS
    | k + 1 => positiveStage k

@[simp] theorem ofPositiveArityStages_stage_zero
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (positiveStage :
      (k : ℕ) → OSIITimeContinuationStage d (k + 1)) :
    (ofPositiveArityStages OS positiveStage).stage 0 =
      canonicalZeroGapTimeContinuationStage OS :=
  rfl

@[simp] theorem ofPositiveArityStages_stage_succ
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (positiveStage :
      (k : ℕ) → OSIITimeContinuationStage d (k + 1))
    (k : ℕ) :
    (ofPositiveArityStages OS positiveStage).stage (k + 1) =
      positiveStage k :=
  rfl

/-- The predecessor stage used to construct an `(q + 2)`-particle Hilbert
field is the stage on the reflected reduced source with `2 * (q + 2) - 1`
time gaps. -/
def reflectedPairStage
    (L : SimultaneousTimeContinuationStageLevel d) :
    OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)) :=
  L.stage ((q + 1) + ((q + 1) + 1))

/-- Every arity in a simultaneous induction level has a local canonical
reduced edge around each compact strict-positive time carrier. -/
def HasCanonicalReducedCompactEdges
    [NeZero d]
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d) : Prop :=
  ∀ k, OSIIChapterV.HasCanonicalReducedCompactStageEdges OS (L.stage k)

/-- Every arity in a simultaneous induction level has a convex complex-time
carrier.  This is the one-chart base invariant used by the first rooted
successor; later successors retain a branchwise convex atlas instead. -/
def HasConvexCarriers
    (L : SimultaneousTimeContinuationStageLevel d) : Prop :=
  ∀ k, Convex ℝ (L.stage k).carrier

/-- To construct the canonical compact-edge invariant at a simultaneous
level, it is enough to supply it at every positive arity. -/
theorem ofPositiveArityStages_hasCanonicalReducedCompactEdges
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (positiveStage :
      (k : ℕ) → OSIITimeContinuationStage d (k + 1))
    (H :
      ∀ k,
        OSIIChapterV.HasCanonicalReducedCompactStageEdges
          OS (positiveStage k)) :
    (ofPositiveArityStages OS positiveStage
      ).HasCanonicalReducedCompactEdges OS := by
  intro k
  cases k with
  | zero =>
      exact
        canonicalZeroGapTimeContinuationStage_hasCanonicalReducedCompactStageEdges
          OS
  | succ k =>
      exact H k

/-- Convexity at every positive arity, together with the canonical full
zero-gap carrier, gives convexity at every arity of the assembled level. -/
theorem ofPositiveArityStages_hasConvexCarriers
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (positiveStage :
      (k : ℕ) → OSIITimeContinuationStage d (k + 1))
    (H : ∀ k, Convex ℝ (positiveStage k).carrier) :
    (ofPositiveArityStages OS positiveStage).HasConvexCarriers := by
  intro k
  cases k with
  | zero =>
      simpa [canonicalZeroGapTimeContinuationStage,
        zeroGapTimeContinuationStage] using
        (convex_univ :
          Convex ℝ
            (Set.univ : Set (OSIITimeGapSpace 0)))
  | succ k =>
      exact H k

end SimultaneousTimeContinuationStageLevel

variable {d q : ℕ} [NeZero d]

/-- The source-specific predecessor contract for translated mixed delta
sources.  It retains only the ordered-current evaluations needed by the mixed
moving-slice continuation, and records that the selected stage is the
simultaneous predecessor stage at the reflected pair arity. -/
structure TranslatedMixedDeltaOrderedSourcePredecessorData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) where
  tailStart : ℕ
  uniformSupport :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        (I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + tailStart)).1)
  sourceEdge :
    UniformCompactTimeMixedOrderedSourceStageData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + tailStart))
  sourceEdge_stage :
    sourceEdge.stage = L.reflectedPairStage (q := q)

/-- A translated mixed-delta predecessor represented by the simultaneous
stage's fixed canonical reduced A0 cutoff.

The support-one property and canonical identity are retained by the mixed
germ constructor. Thus any legacy predecessor carrying a full represented
mixed edge converts to this package without an additional mathematical
hypothesis. -/
structure TranslatedMixedDeltaCanonicalCutoffPredecessorData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) where
  tailStart : ℕ
  sourceEdge :
    UniformCompactTimeMixedCanonicalCutoffStageData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + tailStart))
  sourceEdge_stage :
    sourceEdge.stage = L.reflectedPairStage (q := q)

namespace SimultaneousTimeContinuationStageLevel

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

/-- A simultaneous level carrying all canonical compact-cutoff edges
automatically supplies the reflected-arity predecessor needed by the
translated mixed-delta construction. -/
theorem exists_translatedMixedDeltaCanonicalCutoffPredecessorData
    (H : L.HasCanonicalReducedCompactEdges OS) :
    Nonempty
      (TranslatedMixedDeltaCanonicalCutoffPredecessorData
        L OS I τ hτ) := by
  obtain ⟨tailStart, uniformSupport⟩ :=
    I.exists_tail_translatedPositiveTimeSpatialSource_uniformCompactSupport
      (d := d) τ hτ
  let f :
      (ℕ × SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ) →
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun p =>
      I.translatedPositiveTimeSpatialSource
        τ hτ p.2 (p.1 + tailStart)
  obtain ⟨germ⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData
      OS f uniformSupport
  obtain ⟨edge⟩ :=
    H ((q + 1) + ((q + 1) + 1))
      (tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
      germ.η_compact germ.η_support
  exact ⟨{
    tailStart := tailStart
    sourceEdge := {
      uniformSupport := uniformSupport
      germ := germ
      stageCutoff := edge.cutoff
      stageCutoff_support := edge.cutoff_support
      stage := L.reflectedPairStage
      realRegion := edge.realRegion
      realRegion_open := edge.realRegion_open
      cutoff_support := edge.compactCarrier_subset
      edge := edge.edge
      stageCutoff_one_on := by
        filter_upwards [germ.cutoff_one_on] with u hu
        intro ab x hx
        exact
          edge.reducedTimeCutoffWeight_eq_one_of_auxiliary
            germ.η Set.Subset.rfl x (hu ab x hx) }
    sourceEdge_stage := rfl }⟩

end SimultaneousTimeContinuationStageLevel

namespace TranslatedMixedDeltaPredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

end TranslatedMixedDeltaPredecessorData

namespace TranslatedMixedDeltaOrderedSourcePredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

/-- The ordered-current predecessor already supplies the direct mixed
stage-orbit contract used by the non-circular Gram constructor. -/
noncomputable def toMixedStageOrbitSourceData
    (D : TranslatedMixedDeltaOrderedSourcePredecessorData L OS I τ hτ) :
    UniformCompactTimeMixedStageOrbitSourceData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + D.tailStart)) :=
  D.sourceEdge.toStageOrbitSourceData OS
    (fun p :
        ℕ × SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
      I.translatedPositiveTimeSpatialSource
        τ hτ p.2 (p.1 + D.tailStart))

end TranslatedMixedDeltaOrderedSourcePredecessorData

namespace TranslatedMixedDeltaCanonicalCutoffPredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

/-- The canonical-cutoff predecessor supplies the existing ordered-current
predecessor contract without any global equality between reduced A0
extensions. -/
noncomputable def toOrderedSourcePredecessorData
    (D :
      TranslatedMixedDeltaCanonicalCutoffPredecessorData
        L OS I τ hτ) :
    TranslatedMixedDeltaOrderedSourcePredecessorData L OS I τ hτ where
  tailStart := D.tailStart
  uniformSupport := D.sourceEdge.uniformSupport
  sourceEdge :=
    D.sourceEdge.toOrderedSourceStageData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + D.tailStart))
  sourceEdge_stage := by
    change D.sourceEdge.stage = L.reflectedPairStage
    exact D.sourceEdge_stage

end TranslatedMixedDeltaCanonicalCutoffPredecessorData

namespace TranslatedMixedDeltaSplitPredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

end TranslatedMixedDeltaSplitPredecessorData

namespace TranslatedMixedDeltaOrderedSourcePredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

/-- The source-specific predecessor edge alone constructs the mixed Gram
family and translated holomorphic Hilbert limit. Its diagonal specialization
supplies the norm-square Hilbert fields, so a second represented predecessor
is unnecessary. -/
theorem exists_mixedGram_and_translatedHolomorphicHilbertField
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (D : TranslatedMixedDeltaOrderedSourcePredecessorData L OS I τ hτ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    ∃ G : UniformCompactTimeMixedHilbertGramFamilyData OS
        (fun p :
            ℕ × SchwartzMap
              (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
          I.translatedPositiveTimeSpatialSource
            τ hτ p.2 (p.1 + D.tailStart))
        D.sourceEdge.stage D.sourceEdge.germ,
      ∃ Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS,
        TendstoLocallyUniformlyOn
            (fun N z => G.hilbert.field (N, χ) z)
            Ψ atTop
            (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) ∧
          DifferentiableOn ℂ Ψ
            (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) := by
  let S := D.toMixedStageOrbitSourceData
  obtain ⟨G⟩ :=
    exists_uniformCompactTimeMixedHilbertGramFamilyData_of_stageOrbitSource
      hTowerC hTowerPi OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + D.tailStart))
      D.uniformSupport S
  refine ⟨G, ?_⟩
  exact
    I.exists_translatedHolomorphicHilbertField
      OS τ hτ χ D.tailStart
        D.sourceEdge.stage D.sourceEdge.germ G

end TranslatedMixedDeltaOrderedSourcePredecessorData

end OSIIChapterV
end OSReconstruction
