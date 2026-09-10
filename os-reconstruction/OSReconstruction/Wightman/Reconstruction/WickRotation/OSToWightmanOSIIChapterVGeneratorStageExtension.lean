/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOverlap

















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Local Chapter V generator branches which extend one previous
distribution-valued continuation stage.

The open seed in an overlap is its intersection with the old carrier. Its
nonemptiness is the geometric input needed by the identity theorem. -/
structure GeneratorStageExtensionData
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) where
  domain : GeneratorIndex k → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  distribution :
    GeneratorIndex k →
      OSIITimeGapSpace k → OSIISpatialDistribution d k
  weaklyHolomorphic :
    ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i)
  compatible :
    ∀ i j, Set.EqOn (distribution i) (distribution j)
      (domain i ∩ domain j)
  agreesOnOld :
    ∀ i, Set.EqOn (distribution i) A.distribution
      (domain i ∩ A.carrier)

namespace GeneratorStageExtensionData

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}

/-- Restrict every generator chart to a smaller open domain while retaining
the same distribution-valued branches. -/
noncomputable def restrictDomains
    (C : GeneratorStageExtensionData A)
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (domain_subset : ∀ i, domain i ⊆ C.domain i) :
    GeneratorStageExtensionData A where
  domain := domain
  domain_open := domain_open
  distribution := C.distribution
  weaklyHolomorphic := fun i χ =>
    (C.weaklyHolomorphic i χ).mono (domain_subset i)
  compatible := by
    intro i j z hz
    exact C.compatible i j
      ⟨domain_subset i hz.1, domain_subset j hz.2⟩
  agreesOnOld := by
    intro i z hz
    exact C.agreesOnOld i ⟨domain_subset i hz.1, hz.2⟩

@[simp]
theorem restrictDomains_domain
    (C : GeneratorStageExtensionData A)
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (domain_subset : ∀ i, domain i ⊆ C.domain i)
    (i : GeneratorIndex k) :
    (C.restrictDomains domain domain_open domain_subset).domain i =
      domain i :=
  rfl

@[simp]
theorem restrictDomains_distribution
    (C : GeneratorStageExtensionData A)
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (domain_subset : ∀ i, domain i ⊆ C.domain i)
    (i : GeneratorIndex k) :
    (C.restrictDomains domain domain_open domain_subset).distribution i =
      C.distribution i :=
  rfl

/-- Two independently constructed extensions of the same predecessor agree
on a connected chart overlap whenever that overlap contains a nonempty open
piece of the old carrier. -/
theorem eqOn_of_connectedOverlap
    (C₁ C₂ : GeneratorStageExtensionData A)
    (i j : GeneratorIndex k)
    (overlap_connected :
      IsConnected (C₁.domain i ∩ C₂.domain j))
    (overlap_old_nonempty :
      ((C₁.domain i ∩ C₂.domain j) ∩ A.carrier).Nonempty) :
    Set.EqOn (C₁.distribution i) (C₂.distribution j)
      (C₁.domain i ∩ C₂.domain j) := by
  apply weaklyHolomorphic_eqOn_of_eqOn_open
    ((C₁.domain_open i).inter (C₂.domain_open j))
    overlap_connected
    (((C₁.domain_open i).inter (C₂.domain_open j)).inter
      A.carrier_open)
    overlap_old_nonempty
    Set.inter_subset_left
    (fun χ => (C₁.weaklyHolomorphic i χ).mono Set.inter_subset_left)
    (fun χ => (C₂.weaklyHolomorphic j χ).mono Set.inter_subset_right)
  intro z hz
  exact
    (C₁.agreesOnOld i ⟨hz.1.1, hz.2⟩).trans
      (C₂.agreesOnOld j ⟨hz.1.2, hz.2⟩).symm

/-- Agreement with the old stage on an open overlap seed forces any two
generator branches to agree on their whole connected overlap. -/
theorem compatible_of_agreesOnOld
    (domain : GeneratorIndex k → Set (OSIITimeGapSpace k))
    (domain_open : ∀ i, IsOpen (domain i))
    (distribution :
      GeneratorIndex k →
        OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (weaklyHolomorphic :
      ∀ i, OSIIWeaklyHolomorphicOn (distribution i) (domain i))
    (overlap_connected :
      ∀ i j, IsConnected (domain i ∩ domain j))
    (overlap_old_nonempty :
      ∀ i j, ((domain i ∩ domain j) ∩ A.carrier).Nonempty)
    (agreesOnOld :
      ∀ i, Set.EqOn (distribution i) A.distribution
        (domain i ∩ A.carrier)) :
    ∀ i j, Set.EqOn (distribution i) (distribution j)
      (domain i ∩ domain j) := by
  intro i j
  apply weaklyHolomorphic_eqOn_of_eqOn_open
    ((domain_open i).inter (domain_open j))
    (overlap_connected i j)
    (((domain_open i).inter (domain_open j)).inter A.carrier_open)
    (overlap_old_nonempty i j)
    Set.inter_subset_left
    (fun χ => (weaklyHolomorphic i χ).mono Set.inter_subset_left)
    (fun χ => (weaklyHolomorphic j χ).mono Set.inter_subset_right)
  intro z hz
  exact
    (agreesOnOld i ⟨hz.1.1, hz.2⟩).trans
      (agreesOnOld j ⟨hz.1.2, hz.2⟩).symm

/-- The compatible local branches form the ordinary Chapter V generator
family. -/
noncomputable def toGeneratorFamily
    (C : GeneratorStageExtensionData A) :
    GeneratorFamily d k where
  domain := C.domain
  domain_open := C.domain_open
  distribution := C.distribution
  weaklyHolomorphic := C.weaklyHolomorphic
  compatible := C.compatible

@[simp] theorem toGeneratorFamily_domain
    (C : GeneratorStageExtensionData A)
    (i : GeneratorIndex k) :
    C.toGeneratorFamily.domain i = C.domain i := rfl

@[simp] theorem toGeneratorFamily_distribution
    (C : GeneratorStageExtensionData A)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) :
    C.toGeneratorFamily.distribution i z = C.distribution i z := rfl

/-- Index the previous stage by `none` and the new generator branches by
`some i`. -/
def stageDomain
    (C : GeneratorStageExtensionData A) :
    Option (GeneratorIndex k) → Set (OSIITimeGapSpace k)
  | none => A.carrier
  | some i => C.domain i

/-- Distribution family consisting of the previous stage and all new
generator branches. -/
def stageDistribution
    (C : GeneratorStageExtensionData A) :
    Option (GeneratorIndex k) →
      OSIITimeGapSpace k → OSIISpatialDistribution d k
  | none => A.distribution
  | some i => C.distribution i

theorem stageDomain_open
    (C : GeneratorStageExtensionData A) :
    ∀ p, IsOpen (C.stageDomain p)
  | none => A.carrier_open
  | some i => C.domain_open i

theorem stageDistribution_weaklyHolomorphic
    (C : GeneratorStageExtensionData A) :
    ∀ p, OSIIWeaklyHolomorphicOn
      (C.stageDistribution p) (C.stageDomain p)
  | none => A.weaklyHolomorphic
  | some i => C.weaklyHolomorphic i

/-- The old stage and all generator branches are pairwise compatible on
their complete overlaps. -/
theorem stageCompatible
    (C : GeneratorStageExtensionData A) :
    ∀ p q, Set.EqOn (C.stageDistribution p) (C.stageDistribution q)
      (C.stageDomain p ∩ C.stageDomain q) := by
  intro p q
  cases p with
  | none =>
      cases q with
      | none =>
          intro z hz
          rfl
      | some j =>
          intro z hz
          exact (C.agreesOnOld j ⟨hz.2, hz.1⟩).symm
  | some i =>
      cases q with
      | none =>
          intro z hz
          exact C.agreesOnOld i hz
      | some j =>
          exact C.compatible i j

/-- Carrier obtained by adjoining all generator domains to the previous
stage. -/
def stageCarrier
    (C : GeneratorStageExtensionData A) :
    Set (OSIITimeGapSpace k) :=
  ⋃ p, C.stageDomain p

/-- Every newly adjoined generator chart is contained in the old-plus-
generator union. -/
theorem generatorDomain_subset_stageCarrier
    (C : GeneratorStageExtensionData A)
    (i : GeneratorIndex k) :
    C.domain i ⊆ C.stageCarrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem (some i) hz

theorem stageCarrier_open
    (C : GeneratorStageExtensionData A) :
    IsOpen C.stageCarrier :=
  isOpen_iUnion C.stageDomain_open

/-- Distribution obtained by gluing the previous stage and all generator
branches. -/
def gluedDistribution
    (C : GeneratorStageExtensionData A) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  SCV.glued_iUnion C.stageDomain C.stageDistribution

theorem gluedDistribution_apply
    (C : GeneratorStageExtensionData A)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (fun ζ => C.gluedDistribution ζ χ) =
      SCV.glued_iUnion C.stageDomain
        (fun p ζ => C.stageDistribution p ζ χ) := by
  funext ζ
  classical
  simp only [gluedDistribution, SCV.glued_iUnion]
  split_ifs <;> rfl

theorem gluedDistribution_weaklyHolomorphic
    (C : GeneratorStageExtensionData A) :
    OSIIWeaklyHolomorphicOn C.gluedDistribution C.stageCarrier := by
  intro χ
  rw [C.gluedDistribution_apply χ]
  apply SCV.differentiableOn_glued_iUnion
  · intro z hz
    exact hz
  · exact C.stageDomain_open
  · intro p
    exact C.stageDistribution_weaklyHolomorphic p χ
  · intro p q z hz
    exact congrArg
      (fun T : OSIISpatialDistribution d k => T χ)
      (C.stageCompatible p q hz)

/-- The stage obtained by gluing the local generator branches. -/
noncomputable def toTimeContinuationStage
    (C : GeneratorStageExtensionData A) :
    OSIITimeContinuationStage d k where
  carrier := C.stageCarrier
  carrier_open := C.stageCarrier_open
  distribution := C.gluedDistribution
  weaklyHolomorphic := C.gluedDistribution_weaklyHolomorphic

/-- The new generating-union carrier contains the previous carrier. -/
theorem oldCarrier_subset_newCarrier
    (C : GeneratorStageExtensionData A) :
    A.carrier ⊆ C.toTimeContinuationStage.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem none hz

/-- The new continuation stage is a genuine extension of the previous
stage. -/
theorem newStage_extends_old
    (C : GeneratorStageExtensionData A) :
    Set.EqOn C.toTimeContinuationStage.distribution
      A.distribution A.carrier := by
  exact SCV.glued_iUnion_eqOn C.stageCompatible none

/-- The glued stage agrees with each new generator branch on its whole
domain. -/
theorem newStage_eqOn_generatorDomain
    (C : GeneratorStageExtensionData A)
    (i : GeneratorIndex k) :
    Set.EqOn C.toTimeContinuationStage.distribution
      (C.distribution i) (C.domain i) := by
  exact SCV.glued_iUnion_eqOn C.stageCompatible (some i)

/-- A represented positive-real edge of the previous stage survives the
generator extension unchanged. -/
noncomputable def toTimeContinuationStagePositiveRealEdgeData
    [NeZero d]
    (C : GeneratorStageExtensionData A)
    {W : SchwartzNPoint d k →L[ℂ] ℂ}
    {U : Set (Fin k → ℝ)}
    (E : A.PositiveRealEdgeData W U) :
    C.toTimeContinuationStage.PositiveRealEdgeData W U where
  orbit := E.orbit
  stageEdge := by
    intro τ hτ
    have hold := E.stageEdge τ hτ
    refine ⟨C.oldCarrier_subset_newCarrier hold.1, ?_⟩
    exact (C.newStage_extends_old hold.1).trans hold.2
  represents := E.represents
  pointwiseBounded := E.pointwiseBounded

end GeneratorStageExtensionData

end OSIIChapterV
end OSReconstruction
