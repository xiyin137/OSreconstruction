/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientPullback













noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The closed one-coordinate cross of radius `rho` in a finite real
coefficient space. -/
def osiiCoefficientClosedFlatImaginaryUnion
    (ι : Type) [Fintype ι] (rho : Real) :
    Set (ι -> Real) :=
  {y | exists i, |y i| <= rho ∧ forall j, j ≠ i -> y j = 0}

theorem isClosed_osiiCoefficientClosedFlatImaginaryUnion
    (ι : Type) [Fintype ι] (rho : Real) :
    IsClosed (osiiCoefficientClosedFlatImaginaryUnion ι rho) := by
  rw [show
    osiiCoefficientClosedFlatImaginaryUnion ι rho =
      ⋃ i : ι,
        {y : ι -> Real |
          |y i| <= rho ∧ forall j, j ≠ i -> y j = 0} by
    ext y
    simp [osiiCoefficientClosedFlatImaginaryUnion]]
  apply isClosed_iUnion_of_finite
  intro i
  apply IsClosed.inter
  · have hcontinuous :
        Continuous (fun y : ι -> Real => |y i|) :=
      continuous_abs.comp (continuous_apply i)
    exact isClosed_le hcontinuous continuous_const
  · change IsClosed {y : ι -> Real | forall j, j ≠ i -> y j = 0}
    rw [show
      {y : ι -> Real | forall j, j ≠ i -> y j = 0} =
        ⋂ j : ι, ⋂ (_hji : j ≠ i), {y : ι -> Real | y j = 0} by
      ext y
      simp]
    exact isClosed_iInter fun j =>
      isClosed_iInter fun _hji =>
        isClosed_eq (continuous_apply j) continuous_const

theorem osiiCoefficientClosedFlatImaginaryUnion_subset_flat
    {ι : Type} [Fintype ι]
    {rho alpha : Real}
    (hrho : rho < alpha) :
    osiiCoefficientClosedFlatImaginaryUnion ι rho <=
      fintypeFlatImaginaryUnion ι alpha := by
  rintro y ⟨i, hi, hzero⟩
  exact ⟨i, hi.trans_lt hrho, hzero⟩

/-- A bounded compact piece of the closed coefficient cross. -/
def osiiStrictScalarSeedCoefficientFlatWindow
    (ι : Type) [Fintype ι]
    (R rho : Real) :
    Set (ι -> Complex) :=
  Metric.closedBall 0 R ∩
    SCV.horizontalTube
      (osiiCoefficientClosedFlatImaginaryUnion ι rho)

theorem isCompact_osiiStrictScalarSeedCoefficientFlatWindow
    (ι : Type) [Fintype ι]
    (R rho : Real) :
    IsCompact
      (osiiStrictScalarSeedCoefficientFlatWindow ι R rho) := by
  apply (isCompact_closedBall (0 : ι -> Complex) R).inter_right
  exact
    (isClosed_osiiCoefficientClosedFlatImaginaryUnion ι rho).preimage
      (continuous_pi fun i =>
        Complex.continuous_im.comp (continuous_apply i))

/-- A flat-window inclusion uses only realization of the complete
one-coordinate coefficient cross. -/
theorem strictScalarSeedCoefficientFlatWindow_subset_carrier_of_flat
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (hflat :
      SCV.horizontalTube (fintypeFlatImaginaryUnion ι 1) ⊆
        osiiStrictScalarSeedCoefficientCarrier A seed)
    (R rho : Real)
    (hrho : rho < 1) :
    osiiStrictScalarSeedCoefficientFlatWindow ι R rho ⊆
      osiiStrictScalarSeedCoefficientCarrier A seed := by
  intro r hr
  apply hflat
  exact
    osiiCoefficientClosedFlatImaginaryUnion_subset_flat
      hrho hr.2

/-- Compact-local bounds need no information about how the flat coefficient
cross was produced. -/
theorem
    exists_strictScalarSeedCoefficientFlatWindow_neighborhood_bound_of_flat
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (hflat :
      SCV.horizontalTube (fintypeFlatImaginaryUnion ι 1) ⊆
        osiiStrictScalarSeedCoefficientCarrier A seed)
    (R rho : Real)
    (hrho : rho < 1) :
    exists delta : Real, 0 < delta ∧
      Metric.cthickening delta
          (osiiStrictScalarSeedCoefficientFlatWindow ι R rho) ⊆
        osiiStrictScalarSeedCoefficientCarrier A seed ∧
      exists s : Finset (Nat × Nat), exists C : Real, 0 < C ∧
        ∀ r ∈
            Metric.cthickening delta
              (osiiStrictScalarSeedCoefficientFlatWindow ι R rho),
          ∀ chi :
              SchwartzMap (Section43SpatialSpace d k) Complex,
            ‖osiiStrictScalarSeedCoefficientPairing
                A seed chi r‖ <=
              C * s.sup
                (schwartzSeminormFamily Complex
                  (Section43SpatialSpace d k) Complex) chi := by
  let K :=
    osiiStrictScalarSeedCoefficientFlatWindow ι R rho
  have hK_compact : IsCompact K :=
    isCompact_osiiStrictScalarSeedCoefficientFlatWindow ι R rho
  have hK_subset :
      K ⊆ osiiStrictScalarSeedCoefficientCarrier A seed :=
    strictScalarSeedCoefficientFlatWindow_subset_carrier_of_flat
      A seed hflat R rho hrho
  obtain ⟨delta, hdelta, hdelta_subset⟩ :=
    hK_compact.exists_cthickening_subset_open
      (isOpen_osiiStrictScalarSeedCoefficientCarrier A seed)
      hK_subset
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_seedCoefficientPairing_on_compact
      A seed
      (Metric.cthickening delta K)
      hK_compact.cthickening
      hdelta_subset
  exact
    ⟨delta, hdelta, hdelta_subset, s, C, hC, hbound⟩

namespace GeneratedScalarSeedStageLevelSuccessorData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}

end GeneratedScalarSeedStageLevelSuccessorData

end OSIIChapterV
end OSReconstruction
