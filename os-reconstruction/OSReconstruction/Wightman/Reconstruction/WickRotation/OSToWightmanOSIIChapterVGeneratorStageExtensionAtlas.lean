/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtension




















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A family of genuine fixed-coordinate generator extensions of one
predecessor stage, coherent across every pair of charts and generator
splits. -/
structure GeneratorStageExtensionAtlas
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) where
  chart : Type
  extension : chart → GeneratorStageExtensionData A
  compatible :
    ∀ a b i j,
      Set.EqOn
        ((extension a).distribution i)
        ((extension b).distribution j)
        ((extension a).domain i ∩ (extension b).domain j)

namespace GeneratorStageExtensionAtlas

variable {d k : ℕ}
  {A : OSIITimeContinuationStage d k}

/-- The union, over all extension charts, of the branch for one fixed
generator split. -/
def splitDomain
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  ⋃ a, (B.extension a).domain i

theorem splitDomain_open
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    IsOpen (B.splitDomain i) :=
  isOpen_iUnion fun a => (B.extension a).domain_open i

/-- The distribution-valued branch obtained by gluing all charts belonging
to one generator split. -/
def splitDistribution
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  SCV.glued_iUnion
    (fun a => (B.extension a).domain i)
    (fun a => (B.extension a).distribution i)

theorem splitDistribution_eqOn
    (B : GeneratorStageExtensionAtlas A)
    (a : B.chart)
    (i : GeneratorIndex k) :
    Set.EqOn
      (B.splitDistribution i)
      ((B.extension a).distribution i)
      ((B.extension a).domain i) :=
  SCV.glued_iUnion_eqOn
    (fun b c =>
      B.compatible b c i i)
    a

theorem splitDistribution_apply
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (fun z => B.splitDistribution i z χ) =
      SCV.glued_iUnion
        (fun a => (B.extension a).domain i)
        (fun a z => (B.extension a).distribution i z χ) := by
  funext z
  classical
  simp only [splitDistribution, SCV.glued_iUnion]
  split_ifs <;> rfl

/-- Local weak holomorphy survives the chartwise gluing for one split. -/
theorem splitDistribution_weaklyHolomorphic
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    OSIIWeaklyHolomorphicOn
      (B.splitDistribution i) (B.splitDomain i) := by
  intro χ
  rw [B.splitDistribution_apply i χ]
  apply SCV.differentiableOn_glued_iUnion
  · intro z hz
    exact hz
  · intro a
    exact (B.extension a).domain_open i
  · intro a
    exact (B.extension a).weaklyHolomorphic i χ
  · intro a b z hz
    exact congrArg
      (fun T : OSIISpatialDistribution d k => T χ)
      (B.compatible a b i i hz)

/-- The glued branches for two different splits agree on their complete
overlap.  The two points may be represented by different extension charts. -/
theorem splitDistribution_compatible
    (B : GeneratorStageExtensionAtlas A)
    (i j : GeneratorIndex k) :
    Set.EqOn
      (B.splitDistribution i)
      (B.splitDistribution j)
      (B.splitDomain i ∩ B.splitDomain j) := by
  intro z hz
  rcases Set.mem_iUnion.mp hz.1 with ⟨a, hza⟩
  rcases Set.mem_iUnion.mp hz.2 with ⟨b, hzb⟩
  exact
    (B.splitDistribution_eqOn a i hza).trans
      ((B.compatible a b i j ⟨hza, hzb⟩).trans
        (B.splitDistribution_eqOn b j hzb).symm)

/-- Every glued split branch still agrees with the predecessor on its full
overlap with the old carrier. -/
theorem splitDistribution_agreesOnOld
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    Set.EqOn
      (B.splitDistribution i)
      A.distribution
      (B.splitDomain i ∩ A.carrier) := by
  intro z hz
  rcases Set.mem_iUnion.mp hz.1 with ⟨a, hza⟩
  exact
    (B.splitDistribution_eqOn a i hza).trans
      ((B.extension a).agreesOnOld i ⟨hza, hz.2⟩)

/-- Merge a coherent atlas of fixed-coordinate successors into the ordinary
single successor package used by the Chapter V induction. -/
noncomputable def toStageExtensionData
    (B : GeneratorStageExtensionAtlas A) :
    GeneratorStageExtensionData A where
  domain := B.splitDomain
  domain_open := B.splitDomain_open
  distribution := B.splitDistribution
  weaklyHolomorphic := B.splitDistribution_weaklyHolomorphic
  compatible := B.splitDistribution_compatible
  agreesOnOld := B.splitDistribution_agreesOnOld

@[simp]
theorem toStageExtensionData_domain
    (B : GeneratorStageExtensionAtlas A)
    (i : GeneratorIndex k) :
    B.toStageExtensionData.domain i = B.splitDomain i :=
  rfl

/-- Every local chart domain is retained by the merged successor. -/
theorem chartDomain_subset_domain
    (B : GeneratorStageExtensionAtlas A)
    (a : B.chart)
    (i : GeneratorIndex k) :
    (B.extension a).domain i ⊆
      B.toStageExtensionData.domain i := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨a, hz⟩

/-- Cross-chart compatibility is automatic when every local branch is the
restriction of one common distribution-valued continuation.  This is the
adapter expected from a future stage-wide Hilbert realization. -/
noncomputable def ofCommonContinuation
    {ι : Type}
    (extension : ι → GeneratorStageExtensionData A)
    (common :
      OSIITimeGapSpace k → OSIISpatialDistribution d k)
    (agrees :
      ∀ a i,
        Set.EqOn
          ((extension a).distribution i)
          common
          ((extension a).domain i)) :
    GeneratorStageExtensionAtlas A where
  chart := ι
  extension := extension
  compatible := by
    intro a b i j z hz
    exact
      (agrees a i hz.1).trans
        (agrees b j hz.2).symm

end GeneratorStageExtensionAtlas

end OSIIChapterV
end OSReconstruction
