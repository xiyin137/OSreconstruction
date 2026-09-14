/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOverlap
import OSReconstruction.SCV.ConnectedNeighborhood















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Local Hilbert-valued holomorphic charts with direct pairwise overlap
compatibility.

This is the minimal sheaf-theoretic interface needed to glue fields.  Unlike
`HilbertFieldAtlas`, it does not require every chart to contain or be
determined by one common real slice.  That distinction is essential for
complex-centered anchored continuation charts, whose compatibility is proved
directly from their fixed-anchor scalar identities. -/
structure CompatibleHilbertFieldAtlas
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : ℕ) (ι : Type*) where
  domain : ι → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  field : ι → OSIITimeGapSpace k → H
  field_holomorphic :
    ∀ i, DifferentiableOn ℂ (field i) (domain i)
  compatible :
    ∀ i j, Set.EqOn (field i) (field j) (domain i ∩ domain j)

namespace CompatibleHilbertFieldAtlas

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {k : ℕ} {ι : Type*}

/-- The union covered by all directly compatible Hilbert charts. -/
def coveredDomain (A : CompatibleHilbertFieldAtlas H k ι) :
    Set (OSIITimeGapSpace k) :=
  ⋃ i, A.domain i

/-- The global Hilbert field obtained by choosing any chart containing the
point. -/
def gluedField
    (A : CompatibleHilbertFieldAtlas H k ι) :
    OSIITimeGapSpace k → H :=
  SCV.glued_iUnion A.domain A.field

namespace Covers

variable
  {A : CompatibleHilbertFieldAtlas H k ι}
  {U : Set (OSIITimeGapSpace k)}

end Covers
end CompatibleHilbertFieldAtlas

/-- Local Hilbert-valued holomorphic charts which all realize the same vector
orbit on their real slices. -/
structure HilbertFieldAtlas
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (k : ℕ) (ι : Type*) where
  domain : ι → Set (OSIITimeGapSpace k)
  domain_open : ∀ i, IsOpen (domain i)
  domain_convex : ∀ i, Convex ℝ (domain i)
  domain_conj :
    ∀ i z, z ∈ domain i → SCV.conjMap k z ∈ domain i
  field : ι → OSIITimeGapSpace k → H
  field_holomorphic :
    ∀ i, DifferentiableOn ℂ (field i) (domain i)
  realOrbit : (Fin k → ℝ) → H
  realEdge :
    ∀ i x, SCV.realToComplex x ∈ domain i →
      field i (SCV.realToComplex x) = realOrbit x

namespace HilbertFieldAtlas

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {k : ℕ} {ι : Type*}

/-- Two charts realizing one real orbit agree on their complete overlap. -/
theorem compatible
    (A : HilbertFieldAtlas H k ι)
    (i j : ι) :
    Set.EqOn (A.field i) (A.field j)
      (A.domain i ∩ A.domain j) := by
  intro z hz
  let D : Set (OSIITimeGapSpace k) := A.domain i ∩ A.domain j
  have hD_nonempty : D.Nonempty := ⟨z, hz⟩
  have hD_convex : Convex ℝ D :=
    (A.domain_convex i).inter (A.domain_convex j)
  obtain ⟨x₀, hx₀⟩ :=
    GeneratorFamily.exists_real_mem_of_convex_conjMap_invariant
      hD_convex
      (by
        intro w hw
        exact ⟨A.domain_conj i w hw.1, A.domain_conj j w hw.2⟩)
      hD_nonempty
  let v : H := A.field i z - A.field j z
  have hi :
      DifferentiableOn ℂ
        (fun w => (innerSL ℂ v) (A.field i w)) D := by
    exact
      (differentiableOn_const (c := innerSL ℂ v)).clm_apply
        ((A.field_holomorphic i).mono Set.inter_subset_left)
  have hj :
      DifferentiableOn ℂ
        (fun w => (innerSL ℂ v) (A.field j w)) D := by
    exact
      (differentiableOn_const (c := innerSL ℂ v)).clm_apply
        ((A.field_holomorphic j).mono Set.inter_subset_right)
  have hpair :
      (innerSL ℂ v) (A.field i z) =
        (innerSL ℂ v) (A.field j z) := by
    exact
      SCV.holomorphic_eq_of_eq_on_real_of_connected
        ((A.domain_open i).inter (A.domain_open j))
        (hD_convex.isConnected hD_nonempty)
        hi hj hx₀
        (by
          intro x hx
          rw [A.realEdge i x hx.1, A.realEdge j x hx.2])
        z hz
  have hpair' :
      @inner ℂ H _ v (A.field i z) =
        @inner ℂ H _ v (A.field j z) := by
    simpa [innerSL_apply_apply] using hpair
  have hv : @inner ℂ H _ v v = 0 := by
    rw [show v = A.field i z - A.field j z by rfl]
    rw [inner_sub_right, hpair', sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hv)

/-- Forget the common-real-edge mechanism after it has supplied direct
pairwise compatibility. -/
def toCompatible
    (A : HilbertFieldAtlas H k ι) :
    CompatibleHilbertFieldAtlas H k ι where
  domain := A.domain
  domain_open := A.domain_open
  field := A.field
  field_holomorphic := A.field_holomorphic
  compatible := A.compatible

/-- The union covered by all local Hilbert charts. -/
def coveredDomain (A : HilbertFieldAtlas H k ι) :
    Set (OSIITimeGapSpace k) :=
  ⋃ i, A.domain i

/-- The global Hilbert field obtained by choosing any chart containing the
point.  Compatibility makes the choice immaterial on the covered domain. -/
def gluedField
    (A : HilbertFieldAtlas H k ι) :
    OSIITimeGapSpace k → H :=
  SCV.glued_iUnion A.domain A.field

@[simp]
theorem toCompatible_coveredDomain
    (A : HilbertFieldAtlas H k ι) :
    A.toCompatible.coveredDomain = A.coveredDomain :=
  rfl

@[simp]
theorem toCompatible_gluedField
    (A : HilbertFieldAtlas H k ι) :
    A.toCompatible.gluedField = A.gluedField :=
  rfl

namespace Covers

variable
  {A : HilbertFieldAtlas H k ι}
  {U : Set (OSIITimeGapSpace k)}

end Covers
end HilbertFieldAtlas

end OSIIChapterV
end OSReconstruction
