/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTargetGeometry
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.Thickening



















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction

/-- The bounded compactified germ and any holomorphic continuation of the
original radial real edge agree on every connected finite-coordinate overlap
containing zero. -/
theorem centeredCoefficientGerm_eq_originalExtension_on_connected
    {d k : Nat} [NeZero d] [NeZero k]
    (X : OSIIAxisPairMultiGapFlatCrossData d k)
    {S sigma : Real}
    (P : SCV.StripCompactificationParameters S sigma)
    (shift : Real)
    (u : Fin k -> osiiAxisPairIndex d -> Real)
    (Gamma Gamma0 :
      (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex)
    (hGerm : DifferentiableOn Complex
      (osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma)
      (osiiStep4MultiGapCenteredCoefficientGermDomain P shift u))
    (hreal : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      osiiStep4MultiGapCenteredCoefficientOffset shift u
          (osiiAxisPairSimultaneousLogRealEmbed x) ∈
        Metric.ball 0 P.radius ->
      osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (osiiAxisPairSimultaneousLogRealEmbed x) = X.realEdge x)
    (hGamma0 : DifferentiableOn Complex Gamma0
      (osiiAxisPairMultiGapLogDomain d k))
    (hGamma0real : forall x : Fin k -> osiiAxisPairIndex d -> Real,
      Gamma0 (osiiAxisPairSimultaneousLogRealEmbed x) = X.realEdge x)
    (U : Set
      (Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex))
    (hUopen : IsOpen U)
    (hUconnected : IsConnected U)
    (hUzero :
      (0 : Fin (Fintype.card
        (osiiAxisPairMultiGapIndex d k)) -> Complex) ∈ U)
    (hUgerm : forall z, z ∈ U ->
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
          ((osiiAxisPairMultiGapFinFlattenCLE
            (d := d) (k := k)).symm z) ∈
        osiiStep4MultiGapCenteredCoefficientGermDomain P shift u)
    (hUlog : forall z, z ∈ U ->
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
          ((osiiAxisPairMultiGapFinFlattenCLE
            (d := d) (k := k)).symm z) ∈
        osiiAxisPairMultiGapLogDomain d k) :
    forall z, z ∈ U ->
      osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
          (osiiStep4MultiGapCenteredCoefficientTranslate shift u
            ((osiiAxisPairMultiGapFinFlattenCLE
              (d := d) (k := k)).symm z)) =
        Gamma0
          (osiiStep4MultiGapCenteredCoefficientTranslate shift u
            ((osiiAxisPairMultiGapFinFlattenCLE
              (d := d) (k := k)).symm z)) := by
  let translateFin :=
    fun z : Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
      osiiStep4MultiGapCenteredCoefficientTranslate shift u
        ((osiiAxisPairMultiGapFinFlattenCLE
          (d := d) (k := k)).symm z)
  let F := fun z :
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
    osiiStep4MultiGapCenteredCoefficientGerm P shift u Gamma
      (translateFin z)
  let G := fun z :
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Complex =>
    Gamma0 (translateFin z)
  have htranslate : Differentiable Complex translateFin :=
    differentiable_osiiStep4MultiGapCenteredCoefficientTranslate_fin
      shift u
  have hF : DifferentiableOn Complex F U :=
    hGerm.comp htranslate.differentiableOn hUgerm
  have hG : DifferentiableOn Complex G U :=
    hGamma0.comp htranslate.differentiableOn hUlog
  have hreal_eq : forall x :
      Fin (Fintype.card (osiiAxisPairMultiGapIndex d k)) -> Real,
      (fun j => (x j : Complex)) ∈ U ->
        F (fun j => (x j : Complex)) =
          G (fun j => (x j : Complex)) := by
    intro x hx
    have htranslate_real :=
      osiiStep4MultiGapCenteredCoefficientTranslate_fin_realEmbed
        shift u x
    have hoffset := (hUgerm _ hx).1
    rw [htranslate_real] at hoffset
    dsimp only [F, G, translateFin]
    rw [htranslate_real, hreal _ hoffset, hGamma0real]
  exact SCV.holomorphic_eq_of_eq_on_real_of_connected
    hUopen hUconnected hF hG hUzero hreal_eq

namespace OSIIStep4MultiGapSelectedCommonSlopeData

end OSIIStep4MultiGapSelectedCommonSlopeData

end OSReconstruction
