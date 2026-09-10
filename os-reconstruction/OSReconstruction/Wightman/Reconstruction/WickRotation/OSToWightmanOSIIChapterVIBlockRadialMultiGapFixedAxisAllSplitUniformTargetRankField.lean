/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetSource
import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
















noncomputable section

open Complex Set Topology Filter
open scoped Classical

namespace OSReconstruction

open OSIIChapterV.Section43ProductTimeApproximateIdentity
open OSIIChapterV.Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- One source-indexed side of a ranked generator on a fixed compact time
carrier. -/
structure FixedAxisSplitUniformRankFieldData
    {d : Nat} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (depth rank n : Nat)
    (K : Set (Fin n -> Real)) where
  particle_pos : 0 < n
  domain : Set (Fin (n - 1) -> Complex)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : Fin (n - 1) -> Complex) ∈ domain
  field : OSIIChapterV.UniformCompactTimeSource d n K ->
    (Fin (n - 1) -> Complex) -> OSHilbertSpace OS
  fieldCLM : forall z, z ∈ domain ->
    OSIIChapterV.UniformCompactTimeSource d n K →L[Complex]
      OSHilbertSpace OS
  fieldCLM_apply : forall z hz base,
    fieldCLM z hz base = field base z
  field_differentiable : forall base,
    DifferentiableOn Complex (field base) domain
  source : OSIIChapterV.UniformCompactTimeSource d n K ->
    (Fin (n - 1) -> Real) ->
      euclideanPositiveTimeSubmodule (d := d) n
  source_zero : forall base,
    source base 0 = OSIIChapterV.UniformCompactTimeSource.source base
  source_translation_germ : forall base,
    (fun u => (source base u).1) =ᶠ[nhds 0]
      (fun u =>
        translateSchwartzConfiguration
          (OSIIChapterV.sourceParameterDisplacementCLM
            (fun j : Fin (n - 1) =>
              OSIIChapterV.chronologicalTimeSourceDirectionOfPositive
                (d := d) particle_pos j) u)
          (OSIIChapterV.UniformCompactTimeSource.source base).1)
  source_translation_uniform_germ :
    ∀ᶠ u : Fin (n - 1) -> Real in nhds 0, forall base,
      (source base u).1 =
        translateSchwartzConfiguration
          (OSIIChapterV.sourceParameterDisplacementCLM
            (fun j : Fin (n - 1) =>
              OSIIChapterV.chronologicalTimeSourceDirectionOfPositive
                (d := d) particle_pos j) u)
          (OSIIChapterV.UniformCompactTimeSource.source base).1
  realRegion : Set (Fin (n - 1) -> Real)
  realRegion_open : IsOpen realRegion
  zero_mem_realRegion : (0 : Fin (n - 1) -> Real) ∈ realRegion
  realEdge : forall base,
    OSIIChapterV.HasPositiveTimeSourceRealEdge
      OS (field base) (source base) realRegion
  field_joint_continuous :
    ContinuousOn
      (fun p : (Fin (n - 1) -> Complex) ×
          OSIIChapterV.UniformCompactTimeSource d n K =>
        field p.2 p.1)
      (domain ×ˢ Set.univ)
  rankedFiber_subset : forall left : Fin n -> Real,
    OSIIChapterV.OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed n depth left ->
      OSIIChapterV.osiiTimeArgumentCarrier
          ({OSIIChapterV.osiiMixedArgumentTail left} :
            Set (Fin (n - 1) -> Real)) ⊆ domain

namespace FixedAxisSplitUniformRankFieldData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {depth rank n : Nat}
variable {K : Set (Fin n -> Real)}

/-- Specialize a common source-indexed field family to one source, recovering
the pointwise all-split interface exactly. -/
noncomputable def atSource
    (A : FixedAxisSplitUniformRankFieldData OS depth rank n K)
    (base : OSIIChapterV.UniformCompactTimeSource d n K) :
    FixedAxisSplitRankFieldData OS depth rank n where
  particle_pos := A.particle_pos
  domain := A.domain
  domain_open := A.domain_open
  zero_mem_domain := A.zero_mem_domain
  field := A.field base
  field_differentiable := A.field_differentiable base
  baseSource := OSIIChapterV.UniformCompactTimeSource.source base
  source := A.source base
  source_zero := A.source_zero base
  source_translation_germ := A.source_translation_germ base
  realRegion := A.realRegion
  realRegion_open := A.realRegion_open
  zero_mem_realRegion := A.zero_mem_realRegion
  realEdge := A.realEdge base
  rankedFiber_subset := A.rankedFiber_subset

/-- The source-indexed arity-one field. -/
noncomputable def oneParticle
    (K : Set (Fin 1 -> Real)) :
    FixedAxisSplitUniformRankFieldData OS depth rank 1 K where
  particle_pos := by omega
  domain := Set.univ
  domain_open := isOpen_univ
  zero_mem_domain := Set.mem_univ _
  field := fun base _ =>
    osiiPositiveTimeSingleVectorCLM OS 1
      (OSIIChapterV.UniformCompactTimeSource.source base)
  fieldCLM := fun _ _ =>
    (osiiPositiveTimeSingleVectorCLM OS 1).comp
      (OSIIChapterV.uniformCompactTimeSourceSubmodule d 1 K).subtypeL
  fieldCLM_apply := by
    intro z hz base
    rfl
  field_differentiable := by
    intro base
    exact (by fun_prop : Differentiable Complex
      (fun _ : Fin 0 -> Complex =>
        osiiPositiveTimeSingleVectorCLM OS 1
          (OSIIChapterV.UniformCompactTimeSource.source base))).differentiableOn
  source := fun base _ =>
    OSIIChapterV.UniformCompactTimeSource.source base
  source_zero := fun _ => rfl
  source_translation_germ := by
    intro base
    filter_upwards with u
    have hu : u = 0 := by
      funext j
      exact Fin.elim0 j
    subst u
    simp [OSIIChapterV.sourceParameterDisplacementCLM_apply]
  source_translation_uniform_germ := by
    filter_upwards with u
    intro base
    have hu : u = 0 := by
      funext j
      exact Fin.elim0 j
    subst u
    simp [OSIIChapterV.sourceParameterDisplacementCLM_apply]
  realRegion := Set.univ
  realRegion_open := isOpen_univ
  zero_mem_realRegion := Set.mem_univ _
  realEdge := by
    intro _ _ _
    rfl
  field_joint_continuous := by
    let J : OSIIChapterV.UniformCompactTimeSource d 1 K →L[Complex]
        euclideanPositiveTimeSubmodule (d := d) 1 :=
      (OSIIChapterV.uniformCompactTimeSourceSubmodule d 1 K).subtypeL
    have h : Continuous (fun p : (Fin 0 -> Complex) ×
        OSIIChapterV.UniformCompactTimeSource d 1 K =>
      osiiPositiveTimeSingleVectorCLM OS 1 (J p.2)) :=
      (osiiPositiveTimeSingleVectorCLM OS 1).continuous.comp
        (J.continuous.comp continuous_snd)
    simpa [J, OSIIChapterV.UniformCompactTimeSource.source] using h
  rankedFiber_subset := by
    intro _ _ _ _
    exact Set.mem_univ _

variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

/-- The source-indexed reflected-Gram field for a side with at least two
particles. -/
noncomputable def ofAtlas
    (q : Nat)
    {K : Set (Fin ((q + 1) + 1) -> Real)}
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (A : OSIIChapterV.StrictGeneratedMixedReflectedGramAtlasRankData
      (OS := OS) S depth rank q K) :
    FixedAxisSplitUniformRankFieldData
      OS depth rank ((q + 1) + 1) K where
  particle_pos := by omega
  domain := A.atlas.spatialLinearDomain
  domain_open := A.atlas.spatialLinearDomain_open
  zero_mem_domain := by
    apply A.atlas.initialGramPolydisc_subset_spatialLinearDomain
    exact SCV.center_mem_polydisc
      (fun _ => A.atlas.gram.gramRadius_pos)
  field := fun base z =>
    A.atlas.gram.anchoredAtlasField
      A.atlas.sourceStage.stage A.atlas.sourceStage.germ base z
  fieldCLM := fun z hz =>
    A.atlas.gram.anchoredAtlasFieldContinuousLinearMap
      A.atlas.sourceStage.stage A.atlas.sourceStage.germ z
      hz.1 hz.2.1 hz.2.2
  fieldCLM_apply := by
    intro z hz base
    rfl
  field_differentiable := by
    intro base
    exact
      (A.atlas.gram.anchoredAtlasField_holomorphic
        A.atlas.sourceStage.stage A.atlas.sourceStage.germ base).mono
        (fun _ hz => hz.1)
  source := fun base => OSIIChapterV.localPositiveTimeParameterTranslate
    (OSIIChapterV.UniformCompactTimeSource.source base)
    (fun s : Fin (q + 1) =>
      OSIIChapterV.chronologicalTimeSourceDirection (d := d) s)
  source_zero := fun base =>
    OSIIChapterV.localPositiveTimeParameterTranslate_zero _ _
  source_translation_germ := by
    intro base
    have hbase : OSIIChapterV.HasCompactStrictPositiveDifferenceTimeSupport
        (OSIIChapterV.UniformCompactTimeSource.source base).1 :=
      ⟨K, hK_compact, hK_positive, fun y hy => base.2 y hy⟩
    simpa using
      (OSIIChapterV.eventually_localPositiveTimeParameterTranslate_chronological_coe_eq
        (OSIIChapterV.UniformCompactTimeSource.source base) hbase)
  source_translation_uniform_germ := by
    simpa using
      (OSIIChapterV.eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
        (fun base : OSIIChapterV.UniformCompactTimeSource d ((q + 1) + 1) K =>
          OSIIChapterV.UniformCompactTimeSource.source base)
        (OSIIChapterV.UniformCompactTimeSource.hasUniformCompactStrictPositiveDifferenceTimeSupport
          (K := K) hK_compact hK_positive))
  realRegion := A.atlas.gram.anchoredAtlasRealRegion
    A.atlas.sourceStage.stage A.atlas.sourceStage.germ
  realRegion_open := A.atlas.gram.anchoredAtlasRealRegion_open
    A.atlas.sourceStage.stage A.atlas.sourceStage.germ
  zero_mem_realRegion := mem_of_mem_nhds
    (A.atlas.gram.anchoredAtlasRealRegion_mem_nhds
      A.atlas.sourceStage.stage A.atlas.sourceStage.germ)
  realEdge := fun base => A.atlas.gram.anchoredAtlasField_realEdge
    A.atlas.sourceStage.stage A.atlas.sourceStage.germ base
  field_joint_continuous := A.atlas.continuousOn_anchoredAtlasField_joint
  rankedFiber_subset := by
    intro left hleft
    change OSIIChapterV.osiiTimeArgumentCarrier
        ({OSIIChapterV.osiiMixedArgumentTail left} :
          Set (Fin (q + 1) -> Real)) ⊆
      A.atlas.spatialLinearDomain
    intro z hz
    apply A.coversStrictGeneratedAtRank
    refine ⟨hz.1, ?_⟩
    have harg : OSIIChapterV.osiiTimeArgumentVector z =
        OSIIChapterV.osiiMixedArgumentTail left :=
      Set.mem_singleton_iff.mp hz.2
    have hhead : left 0 = 0 :=
      OSIIChapterV.OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
        (by omega) hleft
    have hcons : Fin.cons 0
        (OSIIChapterV.osiiMixedArgumentTail left) = left := by
      simpa [OSIIChapterV.osiiMixedArgumentTail, hhead] using
        (Fin.cons_self_tail left)
    rw [harg, hcons]
    exact hleft

/-- The arity-independent constructor on an arbitrary compact
strict-positive time carrier. -/
noncomputable def ofCarrier
    (S : C) (depth rank n : Nat)
    (P : OSIIChapterV.StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (hn : 0 < n)
    (K : Set (Fin n -> Real))
    (hK_compact : IsCompact K)
    (hK_positive : K ⊆ section43TimeStrictPositiveRegion n) :
    FixedAxisSplitUniformRankFieldData OS depth rank n K := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => exact oneParticle K
      | succ q =>
          exact ofAtlas q hK_compact hK_positive
            (P.forCarrier q K hK_compact hK_positive)

end FixedAxisSplitUniformRankFieldData

namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]

end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
