/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarBranchAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarSuccessor










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace BoundedScalarBranchAtlasData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}

/-- The compact coefficient window contains zero whenever its strip radius
is positive. -/
theorem zero_mem_coefficientFlatWindow
    {n : Nat} [NeZero n]
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (hrho : 0 < rho) :
    (0 : Fin n -> Complex) ∈
      osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho := by
  constructor
  · rw [Metric.mem_closedBall]
    simp
    exact add_nonneg P.radius_pos.le hrho.le
  · change
      (fun i : Fin n => ((0 : Fin n -> Complex) i).im) ∈
        osiiCoefficientClosedFlatImaginaryUnion (Fin n) rho
    exact ⟨0, by simp [hrho.le], by simp⟩

/-- Atlas coverage of the compact coefficient window produces exactly the
analytic branch input consumed by one bounded ranked successor. -/
noncomputable def toSeedBranchInput
    {n : Nat} {S rho : Real}
    (D : BoundedScalarBranchAtlasData A)
    (P : SCV.StripCompactificationParameters S rho)
    (seed : Fin n -> Fin m -> Real)
    (weight : Fin n -> Real)
    (hcover :
      osiiStrictScalarSeedCoefficientFlatWindow
          (Fin n) (P.radius + rho) rho ⊆
        osiiStrictScalarSeedCoefficientMap seed ⁻¹' D.domain) :
    BoundedStrictScalarSeedBranchInputData A P seed weight := by
  let a : D.chart := Classical.choice D.chart_nonempty
  let U : Set (Fin n -> Complex) :=
    osiiStrictCoefficientGermDomain P ∩
      osiiStrictScalarSeedCoefficientMap seed ⁻¹'
        (A.carrier ∩ (D.chartData a).domain)
  have hmap_cont : Continuous
      (osiiStrictScalarSeedCoefficientMap seed) :=
    (osiiStrictScalarSeedCoefficientMap_differentiable seed).continuous
  have hU_open : IsOpen U :=
    (isOpen_osiiStrictCoefficientGermDomain P).inter
      ((A.carrier_open.inter (D.chartData a).domain_open).preimage hmap_cont)
  have hmap_zero :
      osiiStrictScalarSeedCoefficientMap seed
          (0 : Fin n -> Complex) = 0 := by
    funext j
    simp [osiiStrictScalarSeedCoefficientMap]
  have hzero : (0 : Fin n -> Complex) ∈ U := by
    refine ⟨zero_mem_osiiStrictCoefficientGermDomain P, ?_⟩
    change
      osiiStrictScalarSeedCoefficientMap seed
          (0 : Fin n -> Complex) ∈
        A.carrier ∩ (D.chartData a).domain
    rw [hmap_zero]
    exact ⟨A.zero_mem, (D.chartData a).zero_mem_domain⟩
  let hexists := Metric.isOpen_iff.mp hU_open 0 hzero
  let eps := Classical.choose hexists
  have heps := (Classical.choose_spec hexists).1
  have hball := (Classical.choose_spec hexists).2
  exact {
    branch := D.toFun
    domain := D.domain
    branch_differentiableOn := D.toFun_differentiableOn
    coefficientWindow_subset := hcover
    norm_branch_le := fun r hr => D.norm_toFun_le (hcover hr)
    agreementRadius := eps
    agreementRadius_pos := heps
    agreementBall_subset := fun _r hr =>
      ⟨(hball hr).1, (hball hr).2.1⟩
    realAgreement := by
      intro x hx
      have hxU := hball hx
      exact
        (D.toFun_eqOn a hxU.2.2).trans
          ((D.chartData a).toFun_eq_predecessor_on_overlap
            ⟨hxU.2.2, hxU.2.1⟩) }

end BoundedScalarBranchAtlasData
end OSIIChapterV
end OSReconstruction
