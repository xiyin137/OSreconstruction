/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel


















noncomputable section

open Complex Filter Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

/-- Discarding finitely many scales preserves a factorwise product
approximate identity. -/
noncomputable def tail
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N0 : ℕ) :
    Section43ProductTimeApproximateIdentity n where
  factors N := I.factors (N + N0)
  radius N := I.radius (N + N0)
  factor_nonnegative N := I.factor_nonnegative (N + N0)
  factor_real N := I.factor_real (N + N0)
  factor_integral_one N := I.factor_integral_one (N + N0)
  factor_support N := I.factor_support (N + N0)
  nonnegative N := I.nonnegative (N + N0)
  real N := I.real (N + N0)
  integral_one N := I.integral_one (N + N0)
  support N := I.support (N + N0)
  radius_tendsto :=
    I.radius_tendsto.comp (Filter.tendsto_add_atTop_nat N0)

@[simp]
theorem tail_factors
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N0 N : ℕ) :
    (I.tail N0).factors N = I.factors (N + N0) :=
  rfl

@[simp]
theorem tail_test
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N0 N : ℕ) :
    (I.tail N0).test N = I.test (N + N0) :=
  rfl

@[simp]
theorem tail_toSchwartzTimeApproximateIdentity
    {n : ℕ}
    (I : Section43ProductTimeApproximateIdentity n)
    (N0 : ℕ) :
    (I.tail N0).toSchwartzTimeApproximateIdentity =
      I.toSchwartzTimeApproximateIdentity.tail N0 :=
  rfl

namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The left internal-gap coordinates inherit the corresponding entries of
the full strict-positive anchor. -/
def leftInternalAnchor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Fin (i.n - 1) → ℝ :=
  fun a => anchor (i.leftGlobalIndex a)

/-- The right internal-gap coordinates inherit the corresponding entries of
the full strict-positive anchor. -/
def rightInternalAnchor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Fin (i.m - 1) → ℝ :=
  fun b => anchor (i.rightGlobalIndex b)

theorem leftInternalAnchor_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    A.leftInternalAnchor i ∈
      section43TimeStrictPositiveRegion (i.n - 1) := by
  intro a
  exact A.anchor_positive (i.leftGlobalIndex a)

theorem rightInternalAnchor_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    A.rightInternalAnchor i ∈
      section43TimeStrictPositiveRegion (i.m - 1) := by
  intro b
  exact A.anchor_positive (i.rightGlobalIndex b)

/-- The product approximate identity underlying the anchored left internal
block, with the full family's finite carrier tail already removed. -/
noncomputable def leftInternalProductApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity (i.n - 1) :=
  (I.reindex i.leftGlobalIndex).tail A.carrierData.tailStart

/-- The product approximate identity underlying the anchored right internal
block. -/
noncomputable def rightInternalProductApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity (i.m - 1) :=
  (I.reindex i.rightGlobalIndex).tail A.carrierData.tailStart

@[simp]
theorem leftInternalProductApproximateIdentity_toSchwartz
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    (A.leftInternalProductApproximateIdentity i
      ).toSchwartzTimeApproximateIdentity =
      A.leftInternalApproximateIdentity i :=
  rfl

@[simp]
theorem rightInternalProductApproximateIdentity_toSchwartz
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    (A.rightInternalProductApproximateIdentity i
      ).toSchwartzTimeApproximateIdentity =
      A.rightInternalApproximateIdentity i :=
  rfl

/-- Product-basepoint positive source built directly from one left internal
block of the original anchored packet. -/
noncomputable def leftInternalProductBasepointSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.n - 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.n - 1) + 1) :=
  section43PositiveTimeSpatialSourceCLM d ((i.n - 1) + 1)
    (section43PrependCompactPositiveTimeSource
      normalizedPositiveTimeBasepointCutoff
      (A.leftInternalSource i N).f
      (A.leftInternalSource i N).compact
      (A.leftInternalSource i N).positive)
    (section43SpatialBasepointLiftCLM d (i.n - 1)
      (normalizedSpatialBasepointCutoff d).toSchwartz χ)

@[simp]
theorem leftInternalProductBasepointSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.n - 1)) ℂ) :
    (A.leftInternalProductBasepointSource i N χ).1 =
      productBasepointSpatialFullSourceCLM d (i.n - 1)
        normalizedPositiveTimeBasepointCutoff.f
        (A.leftInternalSource i N).f χ :=
  rfl

/-- Product-basepoint positive source built directly from one right internal
block of the original anchored packet. -/
noncomputable def rightInternalProductBasepointSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.m - 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.m - 1) + 1) :=
  section43PositiveTimeSpatialSourceCLM d ((i.m - 1) + 1)
    (section43PrependCompactPositiveTimeSource
      normalizedPositiveTimeBasepointCutoff
      (A.rightInternalSource i N).f
      (A.rightInternalSource i N).compact
      (A.rightInternalSource i N).positive)
    (section43SpatialBasepointLiftCLM d (i.m - 1)
      (normalizedSpatialBasepointCutoff d).toSchwartz χ)

@[simp]
theorem rightInternalProductBasepointSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.m - 1)) ℂ) :
    (A.rightInternalProductBasepointSource i N χ).1 =
      productBasepointSpatialFullSourceCLM d (i.m - 1)
        normalizedPositiveTimeBasepointCutoff.f
        (A.rightInternalSource i N).f χ :=
  rfl

/-- Fixed-head positive source built from one left internal time block and an
arbitrary full spatial test on the resulting particle block. -/
noncomputable def leftInternalHeadSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.n - 1) + 1) :=
  section43PositiveTimeSpatialSourceCLM d ((i.n - 1) + 1)
    (section43PrependCompactPositiveTimeSource
      normalizedPositiveTimeBasepointCutoff
      (A.leftInternalSource i N).f
      (A.leftInternalSource i N).compact
      (A.leftInternalSource i N).positive)
    χ

@[simp]
theorem leftInternalHeadSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    (A.leftInternalHeadSpatialSource i N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d ((i.n - 1) + 1) χ
        (SCV.prependField normalizedPositiveTimeBasepointCutoff.f
          (A.leftInternalSource i N).f) :=
  rfl

/-- Fixed-head positive source built from one right internal time block and an
arbitrary full spatial test on that particle block. -/
noncomputable def rightInternalHeadSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.m - 1) + 1) :=
  section43PositiveTimeSpatialSourceCLM d ((i.m - 1) + 1)
    (section43PrependCompactPositiveTimeSource
      normalizedPositiveTimeBasepointCutoff
      (A.rightInternalSource i N).f
      (A.rightInternalSource i N).compact
      (A.rightInternalSource i N).positive)
    χ

@[simp]
theorem rightInternalHeadSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    (A.rightInternalHeadSpatialSource i N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d ((i.m - 1) + 1) χ
        (SCV.prependField normalizedPositiveTimeBasepointCutoff.f
          (A.rightInternalSource i N).f) :=
  rfl

/-- At one fixed time scale, the left block product-basepoint construction is
continuous and linear in the reduced spatial test. -/
noncomputable def leftInternalProductBasepointVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d (i.n - 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)).comp
    ((section43PositiveTimeSpatialSourceCLM d ((i.n - 1) + 1)
      (section43PrependCompactPositiveTimeSource
        normalizedPositiveTimeBasepointCutoff
        (A.leftInternalSource i N).f
        (A.leftInternalSource i N).compact
        (A.leftInternalSource i N).positive)).comp
      (section43SpatialBasepointLiftCLM d (i.n - 1)
        (normalizedSpatialBasepointCutoff d).toSchwartz))

@[simp]
theorem leftInternalProductBasepointVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.n - 1)) ℂ) :
    A.leftInternalProductBasepointVectorCLM OS i N χ =
      osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)
        (A.leftInternalProductBasepointSource i N χ) :=
  rfl

/-- At one fixed time scale, the right block product-basepoint construction
is continuous and linear in the reduced spatial test. -/
noncomputable def rightInternalProductBasepointVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d (i.m - 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)).comp
    ((section43PositiveTimeSpatialSourceCLM d ((i.m - 1) + 1)
      (section43PrependCompactPositiveTimeSource
        normalizedPositiveTimeBasepointCutoff
        (A.rightInternalSource i N).f
        (A.rightInternalSource i N).compact
        (A.rightInternalSource i N).positive)).comp
      (section43SpatialBasepointLiftCLM d (i.m - 1)
        (normalizedSpatialBasepointCutoff d).toSchwartz))

@[simp]
theorem rightInternalProductBasepointVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (i.m - 1)) ℂ) :
    A.rightInternalProductBasepointVectorCLM OS i N χ =
      osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)
        (A.rightInternalProductBasepointSource i N χ) :=
  rfl

/-- At a fixed time scale, the direct left fixed-head source is continuous and
linear in its full spatial test. -/
noncomputable def leftInternalHeadSpatialVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)).comp
    (section43PositiveTimeSpatialSourceCLM d ((i.n - 1) + 1)
      (section43PrependCompactPositiveTimeSource
        normalizedPositiveTimeBasepointCutoff
        (A.leftInternalSource i N).f
        (A.leftInternalSource i N).compact
        (A.leftInternalSource i N).positive))

@[simp]
theorem leftInternalHeadSpatialVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    A.leftInternalHeadSpatialVectorCLM OS i N χ =
      osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)
        (A.leftInternalHeadSpatialSource i N χ) :=
  rfl

/-- At a fixed time scale, the direct right fixed-head source is continuous
and linear in its full spatial test. -/
noncomputable def rightInternalHeadSpatialVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)).comp
    (section43PositiveTimeSpatialSourceCLM d ((i.m - 1) + 1)
      (section43PrependCompactPositiveTimeSource
        normalizedPositiveTimeBasepointCutoff
        (A.rightInternalSource i N).f
        (A.rightInternalSource i N).compact
        (A.rightInternalSource i N).positive))

@[simp]
theorem rightInternalHeadSpatialVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    A.rightInternalHeadSpatialVectorCLM OS i N χ =
      osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)
        (A.rightInternalHeadSpatialSource i N χ) :=
  rfl

section CanonicalEdges

variable {q : ℕ}

/- The simultaneous canonical compact-edge invariant supplies all mixed
Gram data required by the product-basepoint producer. Consequently its
time-scale and spatial-truncation bound needs no extra family-specific
analytic hypothesis. -/

/- The simultaneous canonical compact-edge invariant also supplies the
arbitrary-full-spatial fixed-head producer. Consequently every bounded full
spatial family has one norm-square bound uniform in both indices. -/
section PositiveHeadCanonicalEdge

set_option maxHeartbeats 800000

end PositiveHeadCanonicalEdge

/- The canonical compact-edge invariant controls the whole shrinking
product-basepoint family on one real chronological-translation neighborhood,
not only at the zero increment. -/

end CanonicalEdges

/- For a nontrivial left block, the canonical predecessor invariant gives a
bound uniform in both the cofinal shrinking-time tail and the spatial
truncation level. -/

/- For a nontrivial right block, the canonical predecessor invariant gives
the analogous cofinal two-scale Hilbert-vector bound. -/

/- For a nontrivial left block, the canonical predecessor invariant gives a
cofinal bound for every bounded family of full spatial tests. -/

/- For a nontrivial right block, the canonical predecessor invariant gives
the analogous cofinal bound for bounded full spatial families. -/

/- For every nontrivial left internal block, the canonical predecessor
invariant gives one Hilbert-vector bound valid at all time-smearing scales and
all spatial truncation levels. -/

/- For every nontrivial right internal block, the canonical predecessor
invariant gives the analogous all-scale two-index bound. -/

/- Every nontrivial left internal block admits one Hilbert-vector bound valid
at all time-smearing scales for every bounded full spatial family. -/

/- Every nontrivial right internal block admits the analogous all-scale bound
for every bounded full spatial family. -/

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
