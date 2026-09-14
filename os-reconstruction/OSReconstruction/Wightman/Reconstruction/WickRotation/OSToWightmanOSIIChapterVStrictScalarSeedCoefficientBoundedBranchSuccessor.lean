/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientBoundedChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBoundedScalarTargetSuccessor















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace BoundedScalarTargetChartData

variable {m n : Nat} [NeZero n]
variable {B S rho : Real}
variable {A : BoundedScalarContinuationData m B}
variable {P : SCV.StripCompactificationParameters S rho}
variable {F : (Fin m -> Complex) -> Complex}
variable {seed : Fin n -> Fin m -> Real}
variable {w : Fin n -> Real}

/-- Equality on the real points of one coefficient ball promotes to equality
of the two holomorphic coefficient germs on that complete complex ball. -/
theorem germ_eq_predecessor_on_ball_of_real
    (C : BoundedStrictScalarSeedCoefficientChartData
      P F seed w B)
    (eps : Real)
    (heps : 0 < eps)
    (hball :
      Metric.ball (0 : Fin n -> Complex) eps ⊆
        osiiStrictCoefficientGermDomain P ∩
          osiiStrictScalarSeedCoefficientMap seed ⁻¹' A.carrier)
    (hreal : forall x : Fin n -> Real,
      (fun i => (x i : Complex)) ∈
          Metric.ball (0 : Fin n -> Complex) eps ->
        F (osiiStrictScalarSeedCoefficientMap seed
            (fun i => (x i : Complex))) =
          A.toFun (osiiStrictScalarSeedCoefficientMap seed
            (fun i => (x i : Complex)))) :
    Set.EqOn C.germ
      (fun r => A.toFun
        (osiiStrictScalarSeedCoefficientMap seed r))
      (Metric.ball (0 : Fin n -> Complex) eps) := by
  apply SCV.holomorphic_eq_of_eq_on_real_of_connected_finite
    (x₀ := (0 : Fin n -> Real))
    Metric.isOpen_ball (Metric.isConnected_ball heps)
  · exact C.germ_differentiableOn.mono
      (fun r hr => (hball hr).1)
  · exact A.differentiableOn.comp
      (osiiStrictScalarSeedCoefficientMap_differentiable
        seed).differentiableOn
      (fun r hr => (hball hr).2)
  · simpa using
      (Metric.mem_ball_self heps :
        (0 : Fin n -> Complex) ∈ Metric.ball 0 eps)
  · intro x hx
    rw [C.germ_real x (hball hx).1]
    exact hreal x hx

/-- Retarget an independently constructed bounded coefficient MZ branch to
any coefficient point whose radial segment lies in the compactified germ.
The MZ extension and its exact bound do not depend on the originally chosen
positive coefficient target. -/
noncomputable def ofCoefficientLocalAgreementAt
    (C : BoundedStrictScalarSeedCoefficientChartData
      P F seed w B)
    {r0 : Fin n -> Complex}
    (Q : StrictCoefficientTargetConvexChartData P r0)
    (R : StrictCoefficientTargetSectionData seed r0)
    (eps : Real)
    (heps : 0 < eps)
    (hball :
      Metric.ball (0 : Fin n -> Complex) eps ⊆
        osiiStrictCoefficientGermDomain P ∩
          osiiStrictScalarSeedCoefficientMap seed ⁻¹' A.carrier)
    (hlocal :
      Set.EqOn C.germ
        (fun r => A.toFun
          (osiiStrictScalarSeedCoefficientMap seed r))
        (Metric.ball (0 : Fin n -> Complex) eps)) :
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientCLM seed r0) where
  domain := R.ambientDomain Q
  domain_open := R.ambientDomain_open Q
  domain_convex := R.ambientDomain_convex Q
  zero_mem_domain := R.zero_mem_ambientDomain Q
  target_mem_domain := R.target_mem_ambientDomain Q
  toFun := fun z => C.germ (R.lift z)
  toFun_differentiableOn := by
    exact C.germ_differentiableOn.comp
      R.lift.differentiable.differentiableOn
      (fun _z hz => Q.domain_subset hz)
  norm_toFun_le := by
    intro z hz
    exact C.norm_germ_le (Q.domain_subset hz)
  exists_open_eq_predecessor := by
    let U : Set (Fin m -> Complex) :=
      R.ambientDomain Q ∩
        R.lift ⁻¹' Metric.ball (0 : Fin n -> Complex) eps
    have hU_open : IsOpen U :=
      (R.ambientDomain_open Q).inter
        (Metric.isOpen_ball.preimage R.lift.continuous)
    have hU_zero : (0 : Fin m -> Complex) ∈ U := by
      refine ⟨R.zero_mem_ambientDomain Q, ?_⟩
      simpa using
        (Metric.mem_ball_self heps :
          (0 : Fin n -> Complex) ∈ Metric.ball 0 eps)
    refine ⟨U, hU_open, hU_zero, ?_, ?_⟩
    · intro z hz
      refine ⟨hz.1, ?_⟩
      have hmap :
          osiiStrictScalarSeedCoefficientMap seed (R.lift z) = z := by
        simpa using R.rightInverse z
      rw [← hmap]
      exact (hball hz.2).2
    · intro z hz
      change C.germ (R.lift z) = A.toFun z
      calc
        C.germ (R.lift z) =
            A.toFun
              (osiiStrictScalarSeedCoefficientMap seed
                (R.lift z)) := hlocal hz.2
        _ = A.toFun z := by
          apply congrArg A.toFun
          simpa using R.rightInverse z

/-- Build a bounded ambient target chart at the coefficient chart's original
positive target.  This is the production specialization of
`ofCoefficientLocalAgreementAt`. -/
noncomputable def ofCoefficientLocalAgreement
    (C : BoundedStrictScalarSeedCoefficientChartData
      P F seed w B)
    (R : StrictCoefficientTargetSectionData seed
      (osiiStrictScalarSeedCoefficientTarget w))
    (eps : Real)
    (heps : 0 < eps)
    (hball :
      Metric.ball (0 : Fin n -> Complex) eps ⊆
        osiiStrictCoefficientGermDomain P ∩
          osiiStrictScalarSeedCoefficientMap seed ⁻¹' A.carrier)
    (hlocal :
      Set.EqOn C.germ
        (fun r => A.toFun
          (osiiStrictScalarSeedCoefficientMap seed r))
        (Metric.ball (0 : Fin n -> Complex) eps)) :
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientCLM seed
        (osiiStrictScalarSeedCoefficientTarget w)) :=
  ofCoefficientLocalAgreementAt C C.chart R eps heps hball hlocal

end BoundedScalarTargetChartData
end OSIIChapterV
end OSReconstruction
