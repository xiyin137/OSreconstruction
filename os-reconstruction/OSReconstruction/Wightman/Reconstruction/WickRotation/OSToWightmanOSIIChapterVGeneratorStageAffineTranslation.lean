/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageConvexAtlas











noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace GeneratorSpatialApproximationFamily

variable {d k : ℕ}

/-- Translate a generator family in increment coordinates back to absolute
coordinates centered at `center`. -/
noncomputable def uncenter
    (B : GeneratorSpatialApproximationFamily d k)
    (center : Fin k → ℝ) :
    GeneratorSpatialApproximationFamily d k where
  domain := fun i =>
    {z | z + osiiPositiveRealTimeEmbed (-center) ∈ B.domain i}
  domain_open := fun i =>
    (B.domain_open i).preimage (continuous_id.add continuous_const)
  approximation := fun i N z =>
    B.approximation i N
      (z + osiiPositiveRealTimeEmbed (-center))
  approximation_weaklyHolomorphic := by
    intro i N χ
    exact
      (B.approximation_weaklyHolomorphic i N χ).comp
        (differentiable_id.add_const
          (osiiPositiveRealTimeEmbed (-center))).differentiableOn
        (fun _ hz => hz)
  scalarLimit := fun i z χ =>
    B.scalarLimit i
      (z + osiiPositiveRealTimeEmbed (-center)) χ
  locallyUniform := by
    intro i χ
    exact
      (B.locallyUniform i χ).comp
        (fun z => z + osiiPositiveRealTimeEmbed (-center))
        (fun _ hz => hz)
        (continuous_id.add continuous_const).continuousOn

@[simp]
theorem mem_uncenter_domain
    (B : GeneratorSpatialApproximationFamily d k)
    (center : Fin k → ℝ)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    z ∈ (B.uncenter center).domain i ↔
      z + osiiPositiveRealTimeEmbed (-center) ∈ B.domain i :=
  Iff.rfl

theorem uncenter_domain_convex
    (B : GeneratorSpatialApproximationFamily d k)
    (center : Fin k → ℝ)
    (hconvex : ∀ i, Convex ℝ (B.domain i)) :
    ∀ i, Convex ℝ ((B.uncenter center).domain i) := by
  intro i
  exact
    (hconvex i).translate_preimage_left
      (osiiPositiveRealTimeEmbed (-center))

namespace CommonPositiveRealEdgeData

/-- Translate a common centered real edge to the corresponding absolute real
edge. -/
noncomputable def uncenter
    {B : GeneratorSpatialApproximationFamily d k}
    (E : B.CommonPositiveRealEdgeData)
    (center : Fin k → ℝ) :
    (B.uncenter center).CommonPositiveRealEdgeData where
  realRegion := {τ | τ + -center ∈ E.realRegion}
  realRegion_open :=
    E.realRegion_open.preimage (continuous_id.add continuous_const)
  realRegion_nonempty := by
    obtain ⟨u, hu⟩ := E.realRegion_nonempty
    refine ⟨u + center, ?_⟩
    simpa [add_assoc] using hu
  orbit := fun τ => E.orbit (τ + -center)
  scalarLimit_realEdge := by
    intro i τ hτ
    have h := E.scalarLimit_realEdge i (τ + -center) hτ
    constructor
    · simpa [GeneratorSpatialApproximationFamily.uncenter,
        osiiPositiveRealTimeEmbed_add] using h.1
    · intro χ
      simpa [GeneratorSpatialApproximationFamily.uncenter,
        osiiPositiveRealTimeEmbed_add] using h.2 χ

end CommonPositiveRealEdgeData
end GeneratorSpatialApproximationFamily

namespace GeneratorStageExtensionData

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}
  {center : Fin k → ℝ}

/-- Translate an already-proved centered stage extension back to the fixed
coordinates of its predecessor.  Compatibility is transported by the affine
change of variables, so the analytic continuation argument is not repeated
after translation. -/
noncomputable def uncenter
    (C : GeneratorStageExtensionData (A.recenter center)) :
    GeneratorStageExtensionData A where
  domain := fun i =>
    {z | z + osiiPositiveRealTimeEmbed (-center) ∈ C.domain i}
  domain_open := fun i =>
    (C.domain_open i).preimage (continuous_id.add continuous_const)
  distribution := fun i z =>
    C.distribution i
      (z + osiiPositiveRealTimeEmbed (-center))
  weaklyHolomorphic := by
    intro i χ
    exact
      (C.weaklyHolomorphic i χ).comp
        (differentiable_id.add_const
          (osiiPositiveRealTimeEmbed (-center))).differentiableOn
        (fun _ hz => hz)
  compatible := by
    intro i j z hz
    exact C.compatible i j hz
  agreesOnOld := by
    intro i z hz
    have hshift :
        z + osiiPositiveRealTimeEmbed (-center) +
            osiiPositiveRealTimeEmbed center = z := by
      ext q
      simp [osiiPositiveRealTimeEmbed]
    have hcentered :
        z + osiiPositiveRealTimeEmbed (-center) ∈
          (A.recenter center).carrier := by
      change
        z + osiiPositiveRealTimeEmbed (-center) +
            osiiPositiveRealTimeEmbed center ∈ A.carrier
      simpa only [hshift] using hz.2
    have h :=
      C.agreesOnOld i ⟨hz.1, hcentered⟩
    simpa only [OSIITimeContinuationStage.recenter_distribution,
      hshift] using h

@[simp]
theorem mem_uncenter_domain
    (C : GeneratorStageExtensionData (A.recenter center))
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    z ∈ (C.uncenter).domain i ↔
      z + osiiPositiveRealTimeEmbed (-center) ∈ C.domain i :=
  Iff.rfl

@[simp]
theorem mem_uncenter_domain_sub
    (C : GeneratorStageExtensionData (A.recenter center))
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    z ∈ C.uncenter.domain i ↔
      z - osiiPositiveRealTimeEmbed center ∈ C.domain i := by
  have hneg :
      osiiPositiveRealTimeEmbed (-center) =
        -osiiPositiveRealTimeEmbed center := by
    funext q
    simp [osiiPositiveRealTimeEmbed]
  simpa only [sub_eq_add_neg, hneg] using
    C.mem_uncenter_domain i z

end GeneratorStageExtensionData

end OSIIChapterV
end OSReconstruction
