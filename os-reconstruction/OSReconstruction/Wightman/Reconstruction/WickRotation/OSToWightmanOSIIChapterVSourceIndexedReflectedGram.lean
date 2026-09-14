/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVHilbertCauchySeed




















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A source-indexed holomorphic Hilbert family realizing a prescribed
pairwise reflected scalar continuation.

The field domain is shared by all source indices.  Each prescribed scalar
kernel is holomorphic on one shared doubled domain and agrees with the mixed
Hilbert pair kernel throughout the natural doubled field domain. -/
structure SourceIndexedReflectedGramHilbertFieldData
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Type*) (m : ℕ)
    (scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ) where
  domain : Set (Fin m → ℂ)
  domain_open : IsOpen domain
  domain_convex : Convex ℝ domain
  field : ι → (Fin m → ℂ) → H
  field_holomorphic :
    ∀ a, DifferentiableOn ℂ (field a) domain
  scalarDomain : Set (Fin (m + m) → ℂ)
  scalarDomain_open : IsOpen scalarDomain
  scalar_holomorphic :
    ∀ a b, DifferentiableOn ℂ (scalar a b) scalarDomain
  kernelDomain_subset_scalarDomain :
    ∀ (a b : ι),
      reflectedHilbertPairKernelDomain domain domain ⊆ scalarDomain
  scalar_eq_kernel :
    ∀ a b,
      Set.EqOn (scalar a b)
        (reflectedHilbertPairKernel (field a) (field b))
        (reflectedHilbertPairKernelDomain domain domain)

namespace SourceIndexedReflectedGramHilbertFieldData

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} {m : ℕ}
  {scalar : ι → ι → (Fin (m + m) → ℂ) → ℂ}

/-- Pairwise reflected-Gram compatibility propagates from an old chart to a
new convex chart whenever every source-indexed field agrees locally with its
predecessor at the common continuation center.

This is the source-indexed compatibility step needed after constructing each
new field from its diagonal Cauchy data.  The off-diagonal scalar identities
do not need to be rebuilt coefficient-by-coefficient: they follow from local
predecessor agreement and the several-variable identity theorem. -/
theorem scalar_eq_kernel_on_successor
    [CompleteSpace H]
    (P : SourceIndexedReflectedGramHilbertFieldData
      H ι m scalar)
    (center : Fin m → ℂ)
    (hcenter_old : center ∈ P.domain)
    (newDomain : Set (Fin m → ℂ))
    (hnewDomain_open : IsOpen newDomain)
    (hnewDomain_convex : Convex ℝ newDomain)
    (hcenter_new : center ∈ newDomain)
    (newField : ι → (Fin m → ℂ) → H)
    (hnewField_holomorphic :
      ∀ a, DifferentiableOn ℂ (newField a) newDomain)
    (hnewField_eq :
      ∀ a, newField a =ᶠ[𝓝 center] P.field a)
    (hnewKernel_subset :
      ∀ (a b : ι),
        reflectedHilbertPairKernelDomain newDomain newDomain ⊆
          P.scalarDomain)
    (a b : ι) :
    Set.EqOn (scalar a b)
      (reflectedHilbertPairKernel (newField a) (newField b))
      (reflectedHilbertPairKernelDomain newDomain newDomain) := by
  let D :=
    reflectedHilbertPairKernelDomain newDomain newDomain
  have hD_open : IsOpen D :=
    reflectedHilbertPairKernelDomain_open
      hnewDomain_open hnewDomain_open
  have hD_preconnected : IsPreconnected D :=
    (convex_reflectedHilbertPairKernelDomain
      hnewDomain_convex hnewDomain_convex).isPreconnected
  have hcenter_D :
      reflectedCauchyCenter center ∈ D := by
    constructor
    · have hleft :
          star (fun i =>
            reflectedCauchyCenter center
              (Fin.castAdd m i)) = center := by
          funext i
          simp
      simpa only [hleft] using hcenter_new
    · have hright :
          (fun i =>
            reflectedCauchyCenter center
              (Fin.natAdd m i)) = center := by
          funext i
          exact reflectedCauchyCenter_right center i
      simpa only [hright] using hcenter_new
  have hcenter_oldKernel :
      reflectedCauchyCenter center ∈
        reflectedHilbertPairKernelDomain P.domain P.domain := by
    constructor
    · have hleft :
          star (fun i =>
            reflectedCauchyCenter center
              (Fin.castAdd m i)) = center := by
          funext i
          simp
      simpa only [hleft] using hcenter_old
    · have hright :
          (fun i =>
            reflectedCauchyCenter center
              (Fin.natAdd m i)) = center := by
          funext i
          exact reflectedCauchyCenter_right center i
      simpa only [hright] using hcenter_old
  have holdLocal :
      scalar a b =ᶠ[𝓝 (reflectedCauchyCenter center)]
        reflectedHilbertPairKernel (P.field a) (P.field b) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    exact
      ⟨reflectedHilbertPairKernelDomain P.domain P.domain,
        (reflectedHilbertPairKernelDomain_open
          P.domain_open P.domain_open).mem_nhds hcenter_oldKernel,
        P.scalar_eq_kernel a b⟩
  have hnewOldLocal :
      reflectedHilbertPairKernel (newField a) (newField b) =ᶠ[
          𝓝 (reflectedCauchyCenter center)]
        reflectedHilbertPairKernel (P.field a) (P.field b) :=
    reflectedHilbertPairKernel_eventuallyEq
      (hnewField_eq a) (hnewField_eq b)
  have hlocal :
      scalar a b =ᶠ[𝓝 (reflectedCauchyCenter center)]
        reflectedHilbertPairKernel (newField a) (newField b) :=
    holdLocal.trans hnewOldLocal.symm
  have hscalar :
      DifferentiableOn ℂ (scalar a b) D :=
    (P.scalar_holomorphic a b).mono (hnewKernel_subset a b)
  have hkernel :
      DifferentiableOn ℂ
        (reflectedHilbertPairKernel (newField a) (newField b)) D :=
    reflectedHilbertPairKernel_holomorphic
      hnewDomain_open hnewDomain_open
      (hnewField_holomorphic a) (hnewField_holomorphic b)
  exact
    (hscalar.analyticOnNhd_of_finiteDimensional hD_open)
      |>.eqOn_of_preconnected_of_eventuallyEq
        (hkernel.analyticOnNhd_of_finiteDimensional hD_open)
        hD_preconnected hcenter_D hlocal

end SourceIndexedReflectedGramHilbertFieldData

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q : ℕ} [NeZero d]

/-- The concrete compact-time mixed Gram construction is the initial
source-indexed reflected-Gram field package.

The Hilbert domain is restricted to the common Gram polydisc, exactly where
all pairwise identities are simultaneously available.  The doubled scalar
domain remains the complete reflected moving-slice carrier. -/
noncomputable def toInitialSourceIndexedReflectedGramHilbertFieldData
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι →
      euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (G : UniformCompactTimeMixedHilbertGramFamilyData
      OS f stage germ) :
    SourceIndexedReflectedGramHilbertFieldData
      (OSHilbertSpace OS) ι (q + 1)
      (fun a b => (G.cauchy a b).scalar) where
  domain :=
    SCV.Polydisc
      (0 : Fin (q + 1) → ℂ) (fun _ => G.gramRadius)
  domain_open := SCV.polydisc_isOpen
  domain_convex := SCV.polydisc_convex
  field := G.hilbert.field
  field_holomorphic := by
    intro a
    apply (G.hilbert.holomorphic a).mono
    exact
      SCV.polydisc_mono
        (fun _ => le_of_lt G.gramRadius_lt_hilbert)
  scalarDomain := reflectedMovingSliceCarrier stage germ.η
  scalarDomain_open :=
    isOpen_reflectedMovingSliceCarrier
      stage germ.η germ.η_compact
  scalar_holomorphic := G.cauchy_holomorphic
  kernelDomain_subset_scalarDomain := by
    intro a b w hw
    apply G.cauchy_closed a b
    rw [G.cauchy_center a b, G.cauchy_radius a b]
    apply SCV.closedPolydisc_mono
      (fun _ => le_of_lt G.gramRadius_lt_cauchy)
    have hzero :
        reflectedCauchyCenter
            (0 : Fin (q + 1) → ℂ) =
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) := by
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro i
      · simp
      · simpa using
          reflectedCauchyCenter_right
            (0 : Fin (q + 1) → ℂ) i
    have hw' :
        w ∈
          SCV.Polydisc
            (0 : Fin ((q + 1) + (q + 1)) → ℂ)
            (fun _ => G.gramRadius) := by
      rw [← hzero, ← reflectedHilbertKernelDomain_polydisc]
      exact hw
    exact SCV.polydisc_subset_closedPolydisc hw'
  scalar_eq_kernel := by
    intro a b
    have h :=
      G.cauchy_scalar_eqOn_reflectedHilbertPairKernel
        OS f stage germ a b
    have hzero :
        reflectedCauchyCenter
            (0 : Fin (q + 1) → ℂ) =
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) := by
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro i
      · simp
      · simpa using
          reflectedCauchyCenter_right
            (0 : Fin (q + 1) → ℂ) i
    rw [show
      reflectedHilbertPairKernelDomain
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => G.gramRadius))
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => G.gramRadius)) =
        SCV.Polydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ)
          (fun _ => G.gramRadius) by
      rw [reflectedHilbertPairKernelDomain_self,
        reflectedHilbertKernelDomain_polydisc, hzero]]
    exact h

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
