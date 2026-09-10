import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge

/-!
# Uniqueness for represented Chapter V real edges

This module keeps the distributional-uniqueness dependency separate from the
basic positive-real-edge interface.  Two continuous stage orbits representing
the same spacetime distribution agree on the overlap of their open real
regions.
-/

noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIITimeContinuationStage

variable {d k : ℕ} [NeZero d]
variable
  {S₁ S₂ : OSIITimeContinuationStage d k}
  {W : SchwartzNPoint d k →L[ℂ] ℂ}
  {R₁ R₂ : (Fin k → ℝ) → OSIISpatialDistribution d k}
  {U V : Set (Fin k → ℝ)}

/-- Continuous positive-real stage orbits representing the same spacetime
distribution agree pointwise on the overlap of their open real regions. -/
theorem orbit_eqOn_inter_of_sameDistribution
    (h₁ : S₁.HasPositiveRealEdge R₁ U)
    (h₂ : S₂.HasPositiveRealEdge R₂ V)
    (hU_open : IsOpen U)
    (hV_open : IsOpen V)
    (hrep₁ : OSIITimeSpatialRepresentsDistributionOn W R₁ U)
    (hrep₂ : OSIITimeSpatialRepresentsDistributionOn W R₂ V) :
    Set.EqOn R₁ R₂ (U ∩ V) := by
  intro τ hτ
  apply ContinuousLinearMap.ext
  intro χ
  exact
    SCV.eqOn_inter_of_representsDistributionOn
      (W.comp (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
      U V
      (fun u => R₁ u χ)
      (fun u => R₂ u χ)
      hU_open hV_open
      (S₁.continuousOn_positiveRealEdge R₁ U h₁ χ)
      (S₂.continuousOn_positiveRealEdge R₂ V h₂ χ)
      (hrep₁ χ)
      (hrep₂ χ)
      hτ

namespace PositiveRealEdgeData

/-- Positive-real-edge packages representing the same spacetime distribution
have equal named orbits on the overlap of their open real regions. -/
theorem orbit_eqOn_inter_of_sameDistribution
    (E₁ : S₁.PositiveRealEdgeData W U)
    (E₂ : S₂.PositiveRealEdgeData W V)
    (hU_open : IsOpen U)
    (hV_open : IsOpen V) :
    Set.EqOn E₁.orbit E₂.orbit (U ∩ V) :=
  OSIITimeContinuationStage.orbit_eqOn_inter_of_sameDistribution
    E₁.stageEdge E₂.stageEdge hU_open hV_open
    E₁.represents E₂.represents

end PositiveRealEdgeData
end OSIITimeContinuationStage

variable {d k : ℕ} [NeZero d]

omit [NeZero d] in
/-- Equality of a compact-cutoff moving-slice scalar with another holomorphic
scalar on one open real patch propagates through any connected common complex
chart.  This is the scalar comparison step used after identifying a genuine
semigroup/source real edge. -/
theorem osiiStageMovingSliceScalar_eqOn_of_eqOn_open_real
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (F : SchwartzNPoint d k)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (U : Set (Fin k -> Complex))
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hU_moving : U ⊆ osiiStageMovingSliceCarrier A rho)
    (G : (Fin k -> Complex) -> Complex)
    (hG : DifferentiableOn Complex G U)
    (V : Set (Fin k -> Real))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_subset : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U)
    (hreal : forall x, x ∈ V ->
      osiiStageMovingSliceScalar A rho F
          (fun i => (x i : Complex)) =
        G (fun i => (x i : Complex))) :
    forall z, z ∈ U ->
      osiiStageMovingSliceScalar A rho F z = G z := by
  exact
    SCV.holomorphic_eq_of_eq_on_open_real_of_connected_finite
      hU_open hU_connected
      ((differentiableOn_osiiStageMovingSliceScalar
        A rho F hrho_compact).mono hU_moving)
      hG hV_open hV_nonempty hV_subset hreal

/-- A represented positive-real edge reduces a moving-slice/semigroup
comparison to equality of their explicit full-source formulas on one open
real patch.  The preceding totally-real lemma then propagates that equality
through the whole connected common chart. -/
theorem osiiStageMovingSliceScalar_eqOn_of_positiveRealEdge_source_eq
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (edgeRegion : Set (Fin k -> Real))
    (E : A.PositiveRealEdgeData W edgeRegion)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (F : SchwartzNPoint d k)
    (U : Set (Fin k -> Complex))
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hU_moving : U ⊆ osiiStageMovingSliceCarrier A rho)
    (G : (Fin k -> Complex) -> Complex)
    (hG : DifferentiableOn Complex G U)
    (V : Set (Fin k -> Real))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_subset : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U)
    (hrho_shift_support : forall x, x ∈ V ->
      tsupport
          ((SCV.translateSchwartz (-x) rho :
            SchwartzMap (Fin k -> Real) Complex) :
              (Fin k -> Real) -> Complex) ⊆ edgeRegion)
    (hG_real : forall x, x ∈ V ->
      G (fun i => (x i : Complex)) =
        W (section43OrderedPullbackFullCutoffCLM d k
          (SCV.translateSchwartz (-x) rho)
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) (-x)) F))) :
    forall z, z ∈ U ->
      osiiStageMovingSliceScalar A rho F z = G z := by
  apply osiiStageMovingSliceScalar_eqOn_of_eqOn_open_real
    A rho F hrho_compact U hU_open hU_connected hU_moving
    G hG V hV_open hV_nonempty hV_subset
  intro x hx
  simpa only [osiiPositiveRealTimeEmbed] using
    (osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_orderedPullbackFullCutoff_of_edgeData
      A W rho edgeRegion E hrho_compact F x (hrho_shift_support x hx)).trans
      (hG_real x hx).symm

/-- Once a holomorphic semigroup/source branch has been identified on one
represented positive-real patch, any bound proved for that branch transfers
to the moving-slice scalar on the complete connected comparison chart. -/
theorem norm_osiiStageMovingSliceScalar_le_of_positiveRealEdge_source_eq
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (edgeRegion : Set (Fin k -> Real))
    (E : A.PositiveRealEdgeData W edgeRegion)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (F : SchwartzNPoint d k)
    (U : Set (Fin k -> Complex))
    (hU_open : IsOpen U)
    (hU_connected : IsConnected U)
    (hU_moving : U ⊆ osiiStageMovingSliceCarrier A rho)
    (G : (Fin k -> Complex) -> Complex)
    (hG : DifferentiableOn Complex G U)
    (B : Real)
    (hG_norm_le : forall z, z ∈ U -> ‖G z‖ <= B)
    (V : Set (Fin k -> Real))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_subset : forall x, x ∈ V ->
      (fun i => (x i : Complex)) ∈ U)
    (hrho_shift_support : forall x, x ∈ V ->
      tsupport
          ((SCV.translateSchwartz (-x) rho :
            SchwartzMap (Fin k -> Real) Complex) :
              (Fin k -> Real) -> Complex) ⊆ edgeRegion)
    (hG_real : forall x, x ∈ V ->
      G (fun i => (x i : Complex)) =
        W (section43OrderedPullbackFullCutoffCLM d k
          (SCV.translateSchwartz (-x) rho)
          (translateSchwartzConfiguration
            (osiiDifferenceTimeTranslation (d := d) (-x)) F))) :
    forall z, z ∈ U ->
      ‖osiiStageMovingSliceScalar A rho F z‖ <= B := by
  intro z hz
  rw [osiiStageMovingSliceScalar_eqOn_of_positiveRealEdge_source_eq
    A W rho edgeRegion E hrho_compact F U hU_open hU_connected
    hU_moving G hG V hV_open hV_nonempty hV_subset
    hrho_shift_support hG_real z hz]
  exact hG_norm_le z hz

end OSReconstruction
