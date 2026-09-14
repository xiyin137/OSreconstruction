/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import Mathlib.Topology.MetricSpace.Thickening


















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Common geometric data for one source-family Cauchy continuation step.

The dimension is written as `k + 1`, matching the positive-dimensional
Hilbert Cauchy continuation API.  The zero-dimensional one-particle tail is
handled separately by the existing zero-gap construction. -/
structure SourceIndexedComplexCenteredHilbertCauchyData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Type*) (k : ℕ)
    (scalar :
      ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ)
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar) where
  center : Fin (k + 1) → ℂ
  center_mem : center ∈ P.domain
  oldRadius : ℝ
  oldRadius_pos : 0 < oldRadius
  oldClosedPolydisc :
    SCV.closedPolydisc center (fun _ => oldRadius) ⊆ P.domain
  scalarRadius : ℝ
  scalarRadius_pos : 0 < scalarRadius
  scalarClosedPolydisc :
    SCV.closedPolydisc
        (reflectedCauchyCenter center) (fun _ => scalarRadius) ⊆
      P.scalarDomain

namespace SourceIndexedComplexCenteredHilbertCauchyData

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {ι : Type*} {k : ℕ}
  {scalar :
    ι → ι → (Fin ((k + 1) + (k + 1)) → ℂ) → ℂ}
  {P : SourceIndexedReflectedGramHilbertFieldData
    H ι (k + 1) scalar}

/-- A compact family of centers inside an open finite-dimensional complex
domain admits one common positive closed-polydisc radius. -/
theorem exists_uniform_closedPolydisc_subset_open
    {m : ℕ}
    {K U : Set (Fin m → ℂ)}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ r > 0, ∀ center ∈ K,
      SCV.closedPolydisc center (fun _ => r) ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ :=
    hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro center hcenter z hz
  apply hthick
  apply Metric.mem_cthickening_of_dist_le z center δ K hcenter
  have hdist : dist z center ≤ δ / 2 := by
    apply (dist_pi_le_iff (half_pos hδ).le).2
    intro i
    exact (SCV.mem_closedPolydisc_iff.mp hz) i
  linarith

/-- A Hilbert-center segment whose reflected image stays inside the retained
scalar domain admits one common reflected scalar Cauchy radius.

This formulation does not require the complete scalar domain to be convex;
the later generated-domain argument only needs to provide the actual
reflected path inclusion. -/
theorem exists_uniform_reflected_closedPolydisc_along_segment
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    {start target : Fin (k + 1) → ℂ}
    (hreflected :
      ∀ center ∈ segment ℝ start target,
        reflectedCauchyCenter center ∈ P.scalarDomain) :
    ∃ radius > 0,
      ∀ center ∈ segment ℝ start target,
        SCV.closedPolydisc
            (reflectedCauchyCenter center)
            (fun _ => radius) ⊆
          P.scalarDomain := by
  have hsegment :
      IsCompact (segment ℝ start target) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hreflected_continuous :
      Continuous
        (reflectedCauchyCenter :
          (Fin (k + 1) → ℂ) →
            (Fin ((k + 1) + (k + 1)) → ℂ)) := by
    apply continuous_pi
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [reflectedCauchyCenter_left]
      fun_prop
    · intro i
      simp only [reflectedCauchyCenter_right]
      fun_prop
  let K : Set (Fin ((k + 1) + (k + 1)) → ℂ) :=
    reflectedCauchyCenter '' segment ℝ start target
  have hK_compact : IsCompact K :=
    hsegment.image hreflected_continuous
  have hK_subset : K ⊆ P.scalarDomain := by
    rintro _ ⟨center, hcenter, rfl⟩
    exact hreflected center hcenter
  obtain ⟨radius, hradius, huniform⟩ :=
    exists_uniform_closedPolydisc_subset_open
      hK_compact P.scalarDomain_open hK_subset
  refine ⟨radius, hradius, ?_⟩
  intro center hcenter
  exact huniform _ ⟨center, hcenter, rfl⟩

/-- The scalar Cauchy package for one source is obtained from its diagonal
prescribed scalar continuation on the common reflected polydisc. -/
private theorem exists_diagonalScalarData
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    ∃ C : ReflectedCauchyPolydiscData (k + 1),
      C.scalar = scalar a a ∧
        C.center = reflectedCauchyCenter D.center ∧
          C.radius = D.scalarRadius :=
  exists_reflectedCauchyPolydiscData_of_holomorphic
    (scalar a a) (reflectedCauchyCenter D.center)
    D.scalarRadius D.scalarRadius_pos P.scalarDomain
    D.scalarClosedPolydisc (P.scalar_holomorphic a a)

/-- A canonical diagonal scalar Cauchy package for each source. -/
noncomputable def diagonalScalarData
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    ReflectedCauchyPolydiscData (k + 1) :=
  Classical.choose (D.exists_diagonalScalarData a)

@[simp] theorem diagonalScalarData_scalar
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    (D.diagonalScalarData a).scalar = scalar a a :=
  (Classical.choose_spec (D.exists_diagonalScalarData a)).1

@[simp] theorem diagonalScalarData_center
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    (D.diagonalScalarData a).center =
      reflectedCauchyCenter D.center :=
  (Classical.choose_spec (D.exists_diagonalScalarData a)).2.1

@[simp] theorem diagonalScalarData_radius
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    (D.diagonalScalarData a).radius = D.scalarRadius :=
  (Classical.choose_spec (D.exists_diagonalScalarData a)).2.2

/-- The same diagonal Cauchy chart with a caller-supplied bound on the
closed Cauchy polydisc itself.  This is the minimal quantitative input used
by the coefficient estimate. -/
def diagonalScalarDataOfClosedPolydiscBound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    ReflectedCauchyPolydiscData (k + 1) :=
  ReflectedCauchyPolydiscData.ofClosedPolydiscBound
    (scalar a a) (reflectedCauchyCenter D.center)
    D.scalarRadius B D.scalarRadius_pos hB hbound

@[simp] theorem diagonalScalarDataOfClosedPolydiscBound_scalar
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfClosedPolydiscBound a B hB hbound).scalar =
      scalar a a :=
  rfl

@[simp] theorem diagonalScalarDataOfClosedPolydiscBound_center
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfClosedPolydiscBound a B hB hbound).center =
      reflectedCauchyCenter D.center :=
  rfl

@[simp] theorem diagonalScalarDataOfClosedPolydiscBound_radius
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfClosedPolydiscBound a B hB hbound).radius =
      D.scalarRadius :=
  rfl

@[simp] theorem diagonalScalarDataOfClosedPolydiscBound_bound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfClosedPolydiscBound a B hB hbound).bound = B :=
  rfl

/-- A domain-wide scalar bound is a convenient stronger input for the same
exact-bound diagonal Cauchy chart. -/
def diagonalScalarDataOfDomainBound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    ReflectedCauchyPolydiscData (k + 1) :=
  D.diagonalScalarDataOfClosedPolydiscBound a B hB
    (fun w hw => hbound w (D.scalarClosedPolydisc hw))

@[simp] theorem diagonalScalarDataOfDomainBound_scalar
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfDomainBound a B hB hbound).scalar =
      scalar a a :=
  rfl

@[simp] theorem diagonalScalarDataOfDomainBound_center
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfDomainBound a B hB hbound).center =
      reflectedCauchyCenter D.center :=
  rfl

@[simp] theorem diagonalScalarDataOfDomainBound_radius
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfDomainBound a B hB hbound).radius =
      D.scalarRadius :=
  rfl

@[simp] theorem diagonalScalarDataOfDomainBound_bound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    (D.diagonalScalarDataOfDomainBound a B hB hbound).bound = B :=
  rfl

/-- The old pairwise Gram identity supplies the diagonal reflected-kernel
germ at the common continuation center. -/
theorem diagonalScalar_eventuallyEq_reflectedKernel
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    (D.diagonalScalarData a).scalar =ᶠ[
        𝓝 (reflectedCauchyCenter D.center)]
      reflectedHilbertKernel (P.field a) := by
  have hcenterKernel :
      reflectedCauchyCenter D.center ∈
        reflectedHilbertPairKernelDomain P.domain P.domain := by
    constructor
    · have hleft :
          star (fun i =>
            reflectedCauchyCenter D.center
              (Fin.castAdd (k + 1) i)) = D.center := by
          funext i
          simp
      simpa only [hleft] using D.center_mem
    · have hright :
          (fun i =>
            reflectedCauchyCenter D.center
              (Fin.natAdd (k + 1) i)) = D.center := by
          funext i
          exact reflectedCauchyCenter_right D.center i
      simpa only [hright] using D.center_mem
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine
    ⟨reflectedHilbertPairKernelDomain P.domain P.domain,
      (reflectedHilbertPairKernelDomain_open
        P.domain_open P.domain_open).mem_nhds hcenterKernel,
      ?_⟩
  intro w hw
  simpa only [D.diagonalScalarData_scalar,
    reflectedHilbertPairKernel_self] using
      P.scalar_eq_kernel a a hw

/-- The ordinary complex-centered continuation datum for one source, all
sharing the family-level center and radii. -/
noncomputable def diagonalContinuationData
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    ComplexCenteredHilbertCauchyContinuationData H k where
  oldField := P.field a
  oldDomain := P.domain
  oldDomain_open := P.domain_open
  oldField_holomorphic := P.field_holomorphic a
  center := D.center
  oldRadius := D.oldRadius
  oldRadius_pos := D.oldRadius_pos
  oldClosedPolydisc := D.oldClosedPolydisc
  scalarData := D.diagonalScalarData a
  scalar_center := D.diagonalScalarData_center a
  scalarDomain := P.scalarDomain
  scalarDomain_open := P.scalarDomain_open
  scalarClosedPolydisc := by
    simpa only [D.diagonalScalarData_center,
      D.diagonalScalarData_radius] using D.scalarClosedPolydisc
  scalar_holomorphic := by
    simpa only [D.diagonalScalarData_scalar] using
      P.scalar_holomorphic a a
  scalar_eq_reflectedKernel :=
    D.diagonalScalar_eventuallyEq_reflectedKernel a

/-- The complex-centered continuation datum using a prescribed bound on the
diagonal scalar Cauchy polydisc instead of a compactness-selected one. -/
def diagonalContinuationDataOfClosedPolydiscBound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    ComplexCenteredHilbertCauchyContinuationData H k where
  oldField := P.field a
  oldDomain := P.domain
  oldDomain_open := P.domain_open
  oldField_holomorphic := P.field_holomorphic a
  center := D.center
  oldRadius := D.oldRadius
  oldRadius_pos := D.oldRadius_pos
  oldClosedPolydisc := D.oldClosedPolydisc
  scalarData := D.diagonalScalarDataOfClosedPolydiscBound a B hB hbound
  scalar_center :=
    D.diagonalScalarDataOfClosedPolydiscBound_center a B hB hbound
  scalarDomain := P.scalarDomain
  scalarDomain_open := P.scalarDomain_open
  scalarClosedPolydisc := by
    simpa only [D.diagonalScalarDataOfClosedPolydiscBound_center,
      D.diagonalScalarDataOfClosedPolydiscBound_radius] using
      D.scalarClosedPolydisc
  scalar_holomorphic := by
    simpa only [D.diagonalScalarDataOfClosedPolydiscBound_scalar] using
      P.scalar_holomorphic a a
  scalar_eq_reflectedKernel := by
    simpa only [D.diagonalScalarDataOfClosedPolydiscBound_scalar,
      D.diagonalScalarData_scalar] using
      D.diagonalScalar_eventuallyEq_reflectedKernel a

/-- The stronger domain-wide bound specializes the minimal prescribed-bound
continuation datum. -/
def diagonalContinuationDataOfDomainBound
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    ComplexCenteredHilbertCauchyContinuationData H k :=
  D.diagonalContinuationDataOfClosedPolydiscBound a B hB
    (fun w hw => hbound w (D.scalarClosedPolydisc hw))

/-- Replacing the diagonal scalar package by a prescribed closed-polydisc
bound does not change the Hilbert Cauchy polynomials. -/
@[simp] theorem
    diagonalContinuationDataOfClosedPolydiscBound_coefficientFamily
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound :
      ∀ w ∈ SCV.closedPolydisc
          (reflectedCauchyCenter D.center)
          (fun _ => D.scalarRadius),
        ‖scalar a a w‖ ≤ B) :
    (D.diagonalContinuationDataOfClosedPolydiscBound a B hB hbound
      ).coefficientFamily =
      (D.diagonalContinuationData a).coefficientFamily :=
  rfl

/-- Replacing the diagonal scalar package by a prescribed domain bound does
not change the Hilbert Cauchy polynomials.  Only the quantitative scalar
majorant changes. -/
@[simp] theorem diagonalContinuationDataOfDomainBound_coefficientFamily
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ w ∈ P.scalarDomain, ‖scalar a a w‖ ≤ B) :
    (D.diagonalContinuationDataOfDomainBound a B hB hbound
      ).coefficientFamily =
      (D.diagonalContinuationData a).coefficientFamily :=
  rfl

/-- The common absolute successor chart. -/
def successorDomain
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    Set (Fin (k + 1) → ℂ) :=
  SCV.Polydisc D.center (fun _ => D.scalarRadius)

theorem successorDomain_open
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    IsOpen D.successorDomain :=
  SCV.polydisc_isOpen

theorem successorDomain_convex
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    Convex ℝ D.successorDomain :=
  SCV.polydisc_convex

theorem center_mem_successorDomain
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    D.center ∈ D.successorDomain :=
  SCV.center_mem_polydisc (fun _ => D.scalarRadius_pos)

private theorem exists_sourceIncrementField
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    ∃ Ψ : (Fin (k + 1) → ℂ) → H,
      TendstoLocallyUniformlyOn
          (D.diagonalContinuationData a).coefficientFamily.partialSum
          Ψ atTop
          (SCV.Polydisc
            (0 : Fin (k + 1) → ℂ)
            (fun _ => D.scalarRadius)) ∧
        DifferentiableOn ℂ Ψ
          (SCV.Polydisc
            (0 : Fin (k + 1) → ℂ)
            (fun _ => D.scalarRadius)) ∧
        ∀ᶠ increment : Fin (k + 1) → ℂ in 𝓝 0,
          Ψ increment = P.field a (D.center + increment) := by
  obtain ⟨Ψ, hΨ_tendsto, hΨ_hol, hΨ_eq⟩ :=
    (D.diagonalContinuationData a).exists_continuationField
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · simpa only [diagonalContinuationData,
      D.diagonalScalarData_radius] using hΨ_tendsto
  · simpa only [diagonalContinuationData,
      D.diagonalScalarData_radius] using hΨ_hol
  · simpa only [diagonalContinuationData] using hΨ_eq

/-- The increment-coordinate field selected for one source. -/
noncomputable def sourceIncrementField
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    (Fin (k + 1) → ℂ) → H :=
  Classical.choose (D.exists_sourceIncrementField a)

theorem sourceIncrementField_holomorphic
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    DifferentiableOn ℂ (D.sourceIncrementField a)
      (SCV.Polydisc
        (0 : Fin (k + 1) → ℂ)
        (fun _ => D.scalarRadius)) :=
  (Classical.choose_spec (D.exists_sourceIncrementField a)).2.1

theorem sourceIncrementField_eventuallyEq
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    D.sourceIncrementField a =ᶠ[𝓝 0]
      (fun increment => P.field a (D.center + increment)) :=
  (Classical.choose_spec (D.exists_sourceIncrementField a)).2.2

/-- The source-family successor field in absolute coordinates. -/
noncomputable def successorField
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) (z : Fin (k + 1) → ℂ) : H :=
  D.sourceIncrementField a (z - D.center)

theorem successorField_holomorphic
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    DifferentiableOn ℂ (D.successorField a) D.successorDomain := by
  exact
    (D.sourceIncrementField_holomorphic a).comp
      (differentiable_id.sub_const D.center).differentiableOn
      (by
        intro z hz i
        simpa [successorDomain, dist_zero_right,
          Complex.dist_eq] using hz i)

theorem successorField_eventuallyEq
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P)
    (a : ι) :
    D.successorField a =ᶠ[𝓝 D.center] P.field a := by
  simpa only [successorField,
    ComplexCenteredHilbertCauchyContinuationData.absoluteField,
    diagonalContinuationData] using
      (D.diagonalContinuationData a)
        |>.eventually_absoluteField_eq_oldField
          (D.sourceIncrementField a)
          (D.sourceIncrementField_eventuallyEq a)

theorem successorKernelDomain_subset_scalarDomain
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    reflectedHilbertPairKernelDomain
        D.successorDomain D.successorDomain ⊆
      P.scalarDomain := by
  intro w hw
  apply D.scalarClosedPolydisc
  rw [reflectedHilbertPairKernelDomain_self] at hw
  change
    w ∈ reflectedHilbertKernelDomain
      (SCV.Polydisc D.center (fun _ => D.scalarRadius)) at hw
  rw [reflectedHilbertKernelDomain_polydisc] at hw
  exact SCV.polydisc_subset_closedPolydisc hw

/-- One common source-family Cauchy step preserves the complete prescribed
mixed Gram matrix, not only its diagonal. -/
noncomputable def toSuccessor
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar where
  domain := D.successorDomain
  domain_open := D.successorDomain_open
  domain_convex := D.successorDomain_convex
  field := D.successorField
  field_holomorphic := D.successorField_holomorphic
  scalarDomain := P.scalarDomain
  scalarDomain_open := P.scalarDomain_open
  scalar_holomorphic := P.scalar_holomorphic
  kernelDomain_subset_scalarDomain := by
    intro _a _b
    exact D.successorKernelDomain_subset_scalarDomain
  scalar_eq_kernel := by
    intro a b
    exact
      P.scalar_eq_kernel_on_successor
        D.center D.center_mem
        D.successorDomain D.successorDomain_open
        D.successorDomain_convex D.center_mem_successorDomain
        D.successorField D.successorField_holomorphic
        D.successorField_eventuallyEq
        (fun _a _b => D.successorKernelDomain_subset_scalarDomain)
        a b

@[simp] theorem toSuccessor_domain
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    D.toSuccessor.domain = D.successorDomain :=
  rfl

@[simp] theorem toSuccessor_field
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    D.toSuccessor.field = D.successorField :=
  rfl

@[simp] theorem toSuccessor_scalarDomain
    (D : SourceIndexedComplexCenteredHilbertCauchyData
      H ι k scalar P) :
    D.toSuccessor.scalarDomain = P.scalarDomain :=
  rfl

/-- A continuation step can retain a prescribed scalar radius once the
corresponding reflected closed polydisc is known to lie in the scalar
domain.  Only the predecessor Hilbert radius is selected locally. -/
theorem exists_at_with_scalarRadius
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι (k + 1) scalar)
    (center : Fin (k + 1) → ℂ)
    (hcenter : center ∈ P.domain)
    (scalarRadius : ℝ)
    (hscalarRadius : 0 < scalarRadius)
    (hscalarClosed :
      SCV.closedPolydisc
          (reflectedCauchyCenter center)
          (fun _ => scalarRadius) ⊆
        P.scalarDomain) :
    ∃ D : SourceIndexedComplexCenteredHilbertCauchyData
        H ι k scalar P,
      D.center = center ∧ D.scalarRadius = scalarRadius := by
  obtain ⟨oldRadius, holdRadius, holdClosed⟩ :=
    exists_closedPolydisc_subset_open P.domain_open hcenter
  exact
    ⟨{ center := center
       center_mem := hcenter
       oldRadius := oldRadius
       oldRadius_pos := holdRadius
       oldClosedPolydisc := holdClosed
       scalarRadius := scalarRadius
       scalarRadius_pos := hscalarRadius
       scalarClosedPolydisc := hscalarClosed },
      rfl, rfl⟩

end SourceIndexedComplexCenteredHilbertCauchyData

end OSIIChapterV
end OSReconstruction
