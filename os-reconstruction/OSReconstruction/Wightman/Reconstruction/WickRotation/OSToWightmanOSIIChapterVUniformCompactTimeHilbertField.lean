/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageCompactTimeTaylorEndpoint














open Complex Topology Filter
open scoped BigOperators Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- Holomorphic Hilbert fields for a source-indexed compact-time family, all
defined on one common polydisc and carrying one common positive-real edge. -/
structure UniformCompactTimeSourceHilbertFieldFamilyData
    (OS : OsterwalderSchraderAxioms d)
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1)) where
  radius : ℝ
  radius_pos : 0 < radius
  field : ι → (Fin (q + 1) → ℂ) → OSHilbertSpace OS
  taylor :
    ∀ a,
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          (f a)
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r)).partialSum OS)
        (field a) atTop
        (SCV.Polydisc
          (0 : Fin (q + 1) → ℂ) (fun _ => radius))
  holomorphic :
    ∀ a,
      DifferentiableOn ℂ (field a)
        (SCV.Polydisc
          (0 : Fin (q + 1) → ℂ) (fun _ => radius))
  realRegion : Set (Fin (q + 1) → ℝ)
  realRegion_nhds :
    realRegion ∈ 𝓝 (0 : Fin (q + 1) → ℝ)
  realRegion_open : IsOpen realRegion
  realEdge :
    ∀ a,
      HasPositiveTimeSourceRealEdge OS (field a)
        (localPositiveTimeParameterTranslate
          (f a)
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r))
        realRegion

/-- A common diagonal scalar Cauchy family on one open complex neighborhood is
the exact stage-independent analytic input needed to construct uniform
compact-time Hilbert fields.  This factors the Hilbert-space argument away
from both the origin of the scalar real edge and any continuation-stage
presentation used to obtain it. -/
theorem
    exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_cauchyFamily_on_open
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (U : Set (Fin ((q + 1) + (q + 1)) → ℂ))
    (hU_open : IsOpen U)
    (R Rw : ℝ)
    (hR : 0 < R)
    (hRRw : R < Rw)
    (hclosedRw :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => Rw) ⊆
        U)
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (hcenter : ∀ a, (D a).center = 0)
    (hradius : ∀ a, (D a).radius = R)
    (hclosed :
      ∀ a,
        SCV.closedPolydisc
            (D a).center (fun _ => (D a).radius) ⊆
          U)
    (hscalar :
      ∀ a,
        DifferentiableOn ℂ (D a).scalar U)
    (hreal :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice (D a).scalar (D a).center u =
            OS.S (((q + 1) + 1) + ((q + 1) + 1))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM
                    (fun r : Fin (q + 1) =>
                      chronologicalTimeSourceDirection (d := d) r) u)
                  ((f a).1.osConjTensorProduct (f a).1)))) :
    Nonempty (UniformCompactTimeSourceHilbertFieldFamilyData OS f) := by
  have hcompact :
      ∀ a, HasCompactStrictPositiveDifferenceTimeSupport (f a).1 := by
    obtain ⟨K, hK_compact, hK_positive, hK⟩ := hf
    intro a
    exact ⟨K, hK_compact, hK_positive, fun x hx => hK a x hx⟩
  let raw :
      ι → (Fin ((q + 1) + (q + 1)) → ℝ) → ℂ :=
    fun a u =>
      OS.S (((q + 1) + 1) + ((q + 1) + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM
              (fun r : Fin (q + 1) =>
                chronologicalTimeSourceDirection (d := d) r) u)
            ((f a).1.osConjTensorProduct (f a).1)))
  have hfield :
      ∀ a,
        ∃ Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS,
          TendstoLocallyUniformlyOn
              ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
                (f a)
                (fun r : Fin (q + 1) =>
                  chronologicalTimeSourceDirection (d := d) r)).partialSum OS)
              Ψ atTop
              (SCV.Polydisc
                (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius)) ∧
            DifferentiableOn ℂ Ψ
              (SCV.Polydisc
                (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius)) := by
    intro a
    have hreal_a :
        (fun u : Fin ((q + 1) + (q + 1)) → ℝ =>
          realAffineSlice (D a).scalar (D a).center u) =ᶠ[𝓝 0]
          raw a :=
      hreal.mono (fun _ hu => hu a)
    obtain ⟨Ψ, hΨ, hΨ_hol⟩ :=
      PositiveTimeSourceTaylorFamily.exists_holomorphicField_of_realEdge_compactTime
        hTowerC hTowerPi OS (f a) (hcompact a) (D a)
        hU_open (hclosed a) (hscalar a)
        (by simpa [raw] using hreal_a)
    exact ⟨Ψ, hΨ, hΨ_hol⟩
  choose Ψ hΨ hΨ_hol using hfield
  have hcompat :
      ∀ a (z : Fin (q + 1) → ℂ)
        (hincrement :
          ∀ i, ‖reflectedCauchyIncrement z i‖ < (D a).radius),
        ReflectedSourceCauchyCompatibility OS
          (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
            (f a)
            (fun r : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) r) z)
          ((D a).atIncrement
            (reflectedCauchyIncrement z) hincrement) := by
    intro a z hincrement
    have hreal_a :
        (fun u : Fin ((q + 1) + (q + 1)) → ℝ =>
          realAffineSlice (D a).scalar (D a).center u) =ᶠ[𝓝 0]
          raw a :=
      hreal.mono (fun _ hu => hu a)
    apply
      reflectedSourceCauchyCompatibility_of_realEdge_compactTime
        hTowerC hTowerPi OS (f a) (hcompact a) z
    · intro i
      exact reflectedCauchyIncrement_left z i
    · intro i
      exact reflectedCauchyIncrement_right z i
    · exact hU_open
    · exact hclosed a
    · exact hscalar a
    · simpa [raw] using hreal_a
  have hnorm_reflected :=
    eventually_norm_sq_holomorphicField_eq_reflectedScalar_family_of_compatibility
      OS f
      (fun r : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) r)
      D R Rw hR hcenter hradius hRRw
      hU_open hclosedRw hscalar hcompat Ψ hΨ
  have hsource :=
    eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      f hf
  have hnorm :=
    eventually_norm_sq_holomorphicField_eq_chronologicalTranslate_family
      OS f D Ψ hnorm_reflected hsource
      (by simpa [raw] using hreal)
  have hedge :=
    eventually_holomorphicField_eq_chronologicalTranslate_family_compactTime
      hTowerC OS f hf D R hR hradius
      hU_open hclosed hscalar
      (by simpa [raw] using hreal)
      Ψ hΨ hnorm
  change
    {x : Fin (q + 1) → ℝ |
      ∀ a,
        Ψ a (fun i => (x i : ℂ)) =
          osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
            (localPositiveTimeParameterTranslate
              (f a)
              (fun r : Fin (q + 1) =>
                chronologicalTimeSourceDirection (d := d) r) x)} ∈
      𝓝 0 at hedge
  obtain ⟨V, hVsub, hVopen, h0V⟩ := mem_nhds_iff.mp hedge
  exact ⟨{
    radius := R
    radius_pos := hR
    field := Ψ
    taylor := fun a => by
      simpa [hradius a] using hΨ a
    holomorphic := fun a => by
      simpa [hradius a] using hΨ_hol a
    realRegion := V
    realRegion_nhds := hVopen.mem_nhds h0V
    realRegion_open := hVopen
    realEdge := fun a x hx => hVsub hx a }⟩

/-- Compatibility form for scalar Cauchy families obtained from one reflected
moving-slice continuation stage.  The stage contributes only its open carrier;
the Hilbert-field construction itself is the stage-independent theorem above. -/
theorem exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_cauchyFamily
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ
        (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (η : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ)
    (hη_compact :
      HasCompactSupport
        (η : (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
    (R Rw : ℝ)
    (hR : 0 < R)
    (hRRw : R < Rw)
    (hclosedRw :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => Rw) ⊆
        reflectedMovingSliceCarrier stage η)
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (hcenter : ∀ a, (D a).center = 0)
    (hradius : ∀ a, (D a).radius = R)
    (hclosed :
      ∀ a,
        SCV.closedPolydisc
            (D a).center (fun _ => (D a).radius) ⊆
          reflectedMovingSliceCarrier stage η)
    (hscalar :
      ∀ a,
        DifferentiableOn ℂ (D a).scalar
          (reflectedMovingSliceCarrier stage η))
    (hreal :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice (D a).scalar (D a).center u =
            OS.S (((q + 1) + 1) + ((q + 1) + 1))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM
                    (fun r : Fin (q + 1) =>
                      chronologicalTimeSourceDirection (d := d) r) u)
                  ((f a).1.osConjTensorProduct (f a).1)))) :
    Nonempty (UniformCompactTimeSourceHilbertFieldFamilyData OS f) :=
  exists_uniformCompactTimeSourceHilbertFieldFamilyData_of_cauchyFamily_on_open
    hTowerC hTowerPi OS f hf
    (reflectedMovingSliceCarrier stage η)
    (isOpen_reflectedMovingSliceCarrier stage η hη_compact)
    R Rw hR hRRw hclosedRw D hcenter hradius hclosed hscalar hreal

end OSIIChapterV
end OSReconstruction
