import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageEdgeInvariant

/-!
# Recovering the uncut Schwinger value from a moving-slice distribution

A canonical Chapter V stage edge uses one compact positive-time cutoff to
identify the real distribution.  A moving-slice chart uses a second cutoff
whose support must lie inside that represented real neighborhood.  When both
cutoffs equal one on the reduced-time support of an absolute source, the
zero-shift moving-slice distribution is exactly the original uncut Schwinger
functional.

This is the center-value identity needed by the Chapter VI radial mean-value
argument.  It keeps the two auxiliary cutoffs distinct, which is essential:
the support of the stage-edge cutoff need not lie in the neighborhood on
which that same cutoff equals one.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {stage : OSIITimeContinuationStage d k}
variable {compactCarrier : Set (Fin k -> Real)}

/-- A moving-slice cutoff supported in a canonical represented real
neighborhood recovers the uncut Schwinger value whenever its pulled-back
weight is one on the source support. -/
theorem movingSliceDistribution_zero_diffVarReduction_eq_schwinger_of_weight
    (E : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (eta : SchwartzMap (Fin k -> Real) Complex)
    (heta_support :
      tsupport (eta : (Fin k -> Real) -> Complex) ⊆ E.realRegion)
    (heta_compact :
      HasCompactSupport (eta : (Fin k -> Real) -> Complex))
    (f : SchwartzNPoint d (k + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (heta_weight :
      forall x,
        x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
          reducedTimeCutoffWeight (d := d) eta x = 1)
    (hcarrier :
      forall x,
        x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
          reducedTimeProjectionCLM d k x ∈ compactCarrier) :
    osiiStageMovingSliceDistribution
        stage eta heta_compact 0 (diffVarReduction d k f) =
      OS.S (k + 1) ⟨f, hf⟩ := by
  have hzero : 0 ∈ osiiStageMovingSliceCarrier stage eta := by
    intro tau htau
    simpa using
      (E.edge.stageEdge tau (heta_support htau)).1
  rw [osiiStageMovingSliceDistribution_apply_of_mem
    stage eta heta_compact 0 hzero (diffVarReduction d k f)]
  rw [osiiStageMovingSliceScalar_zero_eq_orderedPullbackFullCutoff
    stage
    (orderedTransportDistribution
      (canonicalReducedTimeCutoffSchwingerCLM
        OS E.cutoff E.cutoff_support))
    eta E.realRegion heta_compact heta_support
    E.edge.stage_continuousOn E.edge.stage_pointwiseBounded
    E.edge.stage_represents (diffVarReduction d k f)]
  rw [orderedTransportDistribution_cutoff]
  rw [reducedTimeCutoff_smul_diffVarReduction_eq_of_one_on_tsupport
    eta f heta_weight]
  exact
    E.toCutoffData.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport
      f hf hcarrier

/-- A moving-slice cutoff supported in a canonical represented real
neighborhood recovers the uncut Schwinger value of every source whose
reduced-time support lies in the compact carrier. -/
theorem movingSliceDistribution_zero_diffVarReduction_eq_schwinger
    (E : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (eta : SchwartzMap (Fin k -> Real) Complex)
    (heta_support :
      tsupport (eta : (Fin k -> Real) -> Complex) ⊆ E.realRegion)
    (heta_compact :
      HasCompactSupport (eta : (Fin k -> Real) -> Complex))
    (heta_one : forall tau, tau ∈ compactCarrier -> eta tau = 1)
    (f : SchwartzNPoint d (k + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hcarrier :
      forall x,
        x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
          reducedTimeProjectionCLM d k x ∈ compactCarrier) :
    osiiStageMovingSliceDistribution
        stage eta heta_compact 0 (diffVarReduction d k f) =
      OS.S (k + 1) ⟨f, hf⟩ := by
  have heta_weight :
      forall x,
        x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
          reducedTimeCutoffWeight (d := d) eta x = 1 := by
    intro x hx
    simpa [reducedTimeCutoffWeight] using
      heta_one (reducedTimeProjectionCLM d k x) (hcarrier x hx)
  exact
    movingSliceDistribution_zero_diffVarReduction_eq_schwinger_of_weight
      E eta heta_support heta_compact f hf heta_weight hcarrier

end OSIIChapterV
end OSReconstruction
