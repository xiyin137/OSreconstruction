/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtensionAtlas


















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The explicit block witnesses giving one open convex chronological chart
through a prescribed radial target. -/
structure RadialChronologicalConvexChartData
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k) where
  leftDomain : Set (Fin (i.n - 1) → ℂ)
  leftDomain_open : IsOpen leftDomain
  leftDomain_convex : Convex ℝ leftDomain
  left_zero_mem : 0 ∈ leftDomain
  leftDomain_subset : leftDomain ⊆ E.leftDomain i
  rightDomain : Set (Fin (i.m - 1) → ℂ)
  rightDomain_open : IsOpen rightDomain
  rightDomain_convex : Convex ℝ rightDomain
  right_zero_mem : 0 ∈ rightDomain
  rightDomain_subset : rightDomain ⊆ E.rightDomain i
  bridge_positive :
    0 <
      ((i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i z)).1).re
  target_left_mem :
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
      leftDomain
  target_right_mem :
    (i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i z)).2.2 ∈
      rightDomain

namespace RadialChronologicalConvexChartData

variable
  {E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
  {i : GeneratorIndex k}
  {z : OSIITimeGapSpace k}

/-- The chronological pullback of the chart's two convex block witnesses. -/
def domain
    (C : RadialChronologicalConvexChartData E i z) :
    Set (OSIITimeGapSpace k) :=
  generatorChronologicalParameterComplexCLE i ⁻¹'
    generatorSemigroupDomain i C.leftDomain C.rightDomain

theorem domain_open
    (C : RadialChronologicalConvexChartData E i z) :
    IsOpen C.domain :=
  (isOpen_generatorSemigroupDomain i
      C.leftDomain_open C.rightDomain_open).preimage
    (generatorChronologicalParameterComplexCLE i).continuous

theorem domain_subset
    (C : RadialChronologicalConvexChartData E i z) :
    C.domain ⊆ E.radialChronologicalDomain i :=
  E.chronologicalWitnessDomain_subset_radialChronologicalDomain i
    C.leftDomain_open C.leftDomain_convex C.left_zero_mem
    C.leftDomain_subset
    C.rightDomain_open C.rightDomain_convex C.right_zero_mem
    C.rightDomain_subset

end RadialChronologicalConvexChartData

/-- Radial membership supplies an explicit open convex chronological witness
chart through the target. -/
theorem nonempty_radialChronologicalConvexChartData
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ E.radialChronologicalDomain i) :
    Nonempty (RadialChronologicalConvexChartData E i z) := by
  rcases hz with ⟨hbridge, hleft, hright⟩
  change
    star
        (i.splitCoordinatesCLM
          (generatorChronologicalParameterComplexCLE i z)).2.1 ∈
      openZeroConvexKernel (E.leftDomain i) at hleft
  rcases hleft with
    ⟨U, hU_open, hU_convex, h0U, hU_subset, hzU⟩
  rcases hright with
    ⟨V, hV_open, hV_convex, h0V, hV_subset, hzV⟩
  exact
    ⟨{
      leftDomain := U
      leftDomain_open := hU_open
      leftDomain_convex := hU_convex
      left_zero_mem := h0U
      leftDomain_subset := hU_subset
      rightDomain := V
      rightDomain_open := hV_open
      rightDomain_convex := hV_convex
      right_zero_mem := h0V
      rightDomain_subset := hV_subset
      bridge_positive := hbridge
      target_left_mem := hzU
      target_right_mem := hzV }⟩

/-- Choose one explicit convex witness chart for a radial target. -/
noncomputable def selectedRadialChronologicalConvexChartData
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ E.radialChronologicalDomain i) :
    RadialChronologicalConvexChartData E i z :=
  Classical.choice
    (E.nonempty_radialChronologicalConvexChartData i hz)

/-- A radial target together with its membership proof. -/
abbrev RadialChronologicalTarget
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (i : GeneratorIndex k) :=
  {z : OSIITimeGapSpace k // z ∈ E.radialChronologicalDomain i}

end GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

/-- Keep one selected generator split on a prescribed domain and make every
other split empty. -/
def singleGeneratorChartDomain
    {k : ℕ}
    (selected : GeneratorIndex k)
    (domain : Set (OSIITimeGapSpace k))
    (i : GeneratorIndex k) :
    Set (OSIITimeGapSpace k) :=
  if i = selected then domain else ∅

@[simp]
theorem singleGeneratorChartDomain_selected
    {k : ℕ}
    (selected : GeneratorIndex k)
    (domain : Set (OSIITimeGapSpace k)) :
    singleGeneratorChartDomain selected domain selected = domain := by
  simp [singleGeneratorChartDomain]

theorem singleGeneratorChartDomain_eq_empty
    {k : ℕ}
    (selected : GeneratorIndex k)
    (domain : Set (OSIITimeGapSpace k))
    (i : GeneratorIndex k)
    (hi : i ≠ selected) :
    singleGeneratorChartDomain selected domain i = ∅ := by
  simp [singleGeneratorChartDomain, hi]

namespace GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {A : OSIITimeContinuationStage d k}

namespace RadialChronologicalConvexChartData

variable
  {E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k}
  {i : GeneratorIndex k}
  {z : OSIITimeGapSpace k}

/-- Restrict a genuine radial extension to one convex target chart and one
generator split. -/
noncomputable def toSingleGeneratorStageExtensionData
    (C : RadialChronologicalConvexChartData E i z)
    (B : GeneratorStageExtensionData A)
    (hradial : E.radialChronologicalDomain i ⊆ B.domain i) :
    GeneratorStageExtensionData A :=
  B.restrictDomains
    (singleGeneratorChartDomain i C.domain)
    (by
      intro j
      by_cases hj : j = i
      · subst j
        simpa using C.domain_open
      · rw [singleGeneratorChartDomain_eq_empty i C.domain j hj]
        exact isOpen_empty)
    (by
      intro j w hw
      by_cases hj : j = i
      · subst j
        apply hradial
        apply C.domain_subset
        simpa using hw
      · change
          w ∈ singleGeneratorChartDomain i C.domain j at hw
        rw [singleGeneratorChartDomain_eq_empty
          i C.domain j hj] at hw
        exact hw.elim)

@[simp]
theorem toSingleGeneratorStageExtensionData_domain_selected
    (C : RadialChronologicalConvexChartData E i z)
    (B : GeneratorStageExtensionData A)
    (hradial : E.radialChronologicalDomain i ⊆ B.domain i) :
    (C.toSingleGeneratorStageExtensionData B hradial).domain i =
      C.domain :=
  singleGeneratorChartDomain_selected i C.domain

end RadialChronologicalConvexChartData

/-- Index all selected convex charts at every generator split. -/
abbrev RadialChronologicalConvexChartIndex
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k) :=
  Σ i : GeneratorIndex k, RadialChronologicalTarget E i

/-- The selected convex chart extension associated to one split and one
radial target. -/
noncomputable def selectedRadialChronologicalConvexChartExtension
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (B : GeneratorStageExtensionData A)
    (hradial : ∀ i, E.radialChronologicalDomain i ⊆ B.domain i)
    (a : RadialChronologicalConvexChartIndex E) :
    GeneratorStageExtensionData A :=
  let C :=
    E.selectedRadialChronologicalConvexChartData
      a.1 a.2.1 a.2.2
  C.toSingleGeneratorStageExtensionData B (hradial a.1)

/-- A genuine radial stage extension is the common continuation behind a
coherent atlas of single-split open convex target charts. -/
noncomputable def radialChronologicalConvexExtensionAtlas
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (B : GeneratorStageExtensionData A)
    (hradial : ∀ i, E.radialChronologicalDomain i ⊆ B.domain i) :
    GeneratorStageExtensionAtlas A :=
  GeneratorStageExtensionAtlas.ofCommonContinuation
    (fun a =>
      E.selectedRadialChronologicalConvexChartExtension
        B hradial a)
    B.toTimeContinuationStage.distribution
    (by
      intro a j w hw
      by_cases hj : j = a.1
      · subst j
        have hwB :
            w ∈ B.domain a.1 := by
          apply hradial a.1
          apply
            (E.selectedRadialChronologicalConvexChartData
              a.1 a.2.1 a.2.2).domain_subset
          simpa [
            selectedRadialChronologicalConvexChartExtension] using hw
        exact
          (B.newStage_eqOn_generatorDomain a.1 hwB).symm
      · have hwempty :
            w ∈ (∅ : Set (OSIITimeGapSpace k)) := by
          change
            w ∈
              singleGeneratorChartDomain a.1
                (E.selectedRadialChronologicalConvexChartData
                  a.1 a.2.1 a.2.2).domain j at hw
          rw [singleGeneratorChartDomain_eq_empty
            a.1
            (E.selectedRadialChronologicalConvexChartData
              a.1 a.2.1 a.2.2).domain
            j hj] at hw
          exact hw
        exact hwempty.elim)

@[simp]
theorem radialChronologicalConvexExtensionAtlas_extension
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k)
    (B : GeneratorStageExtensionData A)
    (hradial : ∀ i, E.radialChronologicalDomain i ⊆ B.domain i)
    (a : RadialChronologicalConvexChartIndex E) :
    (E.radialChronologicalConvexExtensionAtlas B hradial
      ).extension a =
      E.selectedRadialChronologicalConvexChartExtension B hradial a :=
  rfl

end GeneratorOpenHilbertFieldScaleFamilyRealEdgeData

end OSIIChapterV
end OSReconstruction
