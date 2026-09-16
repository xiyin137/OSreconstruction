/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman










noncomputable section

open Complex MeasureTheory

namespace OSReconstruction
namespace OSIIReducedForwardTubeBoundaryData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
variable {W : SchwartzNPoint d k →L[Complex] Complex}

/-- At two or more full points, the same physical kernel's glued Euclidean
density recovers every zero-diagonal Schwartz test by absolute integration. -/
theorem euclideanDensity_reproducesZeroDiagonal_of_pos
    (H : OSIIReducedForwardTubeBoundaryData W)
    (lgc : OSLinearGrowthCondition d OS)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (f : ZeroDiagonalSchwartz d (k + 1)) :
    OS.S (k + 1) f = ∫ x : NPointDomain d (k + 1), H.euclideanDensity x * f.1 x := by
  obtain ⟨C, N, M, hC, hbound⟩ := H.euclideanDensity_exists_weighted_bound lgc Hstage Rstage
  let S := fun z : Fin (k + 1) -> Fin (d + 1) -> Complex =>
    H.euclideanDensity (fun j => osiiAxisPairWickProjection (z j))
  have hS (x : NPointDomain d (k + 1)) :
      S (fun j => wickRotatePoint (x j)) = H.euclideanDensity x := by
    dsimp [S]
    congr 1
    ext j mu
    simp [osiiAxisPairWickProjection, osiiAxisPairInverseWickBlock_wickRotatePoint]
  let E : ACROneEuclideanWeightedKernelData S :=
    { C_bd := C
      N := N
      q := M
      C_bd_pos := hC
      measurable := by
        simpa only [hS] using
          (H.euclideanDensity_measurable Hstage Rstage).aestronglyMeasurable
      weighted_bound := by
        filter_upwards with x
        rw [hS]
        exact hbound x }
  have h01 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have hval := congrArg Fin.val h
    exact NeZero.ne k (by simpa using hval.symm)
  have hcoin : (CoincidenceLocus d (k + 1)).Nonempty := ⟨0, 0, Fin.last k, h01, rfl⟩
  have hrecovery := E.reproducesZeroDiagonal_of_orderedCompactProducts OS (k + 1) hcoin (by
    intro P
    simpa only [hS] using (H.orderedCompactProduct_euclideanDensity_pairing Hstage Rstage P).symm) f
  simpa only [hS] using hrecovery

omit [NeZero k] in
theorem euclideanDensity_zeroGap_eq
    {W0 : SchwartzNPoint d 0 →L[Complex] Complex}
    {stage0 : OSIITimeContinuationStage d 0}
    (H : OSIIReducedForwardTubeBoundaryData W0)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage0)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage0) H)
    (x : NPointDomain d 1) : H.euclideanDensity x = H.kernel 0 := by
  let i : OSIIEuclideanOrderIndex d 0 := (⟨1, by simp, by simp⟩, Equiv.refl _)
  rw [H.euclideanDensity_eqOn Hstage Rstage i (fun j => Fin.elim0 j)]
  exact congrArg H.kernel (Subsingleton.elim _ _)

omit [NeZero k] in
/-- The zero-gap density keeps the original one-point scalar. Compact
Schwartz density supplies the full one-point pairing without normalizing it. -/
theorem euclideanDensity_zeroGap_reproducesZeroDiagonal
    {W0 : SchwartzNPoint d 0 →L[Complex] Complex}
    {stage0 : OSIITimeContinuationStage d 0}
    (H : OSIIReducedForwardTubeBoundaryData W0)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage0)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage0) H)
    (f : ZeroDiagonalSchwartz d 1) :
    OS.S 1 f = ∫ x : NPointDomain d 1, H.euclideanDensity x * f.1 x := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) Real (SpacetimeDim d)
  let J : SchwartzSpacetime d →L[Complex] ZeroDiagonalSchwartz d 1 :=
    (onePointToFin1CLM d).codRestrict (zeroDiagonalSubmodule d 1)
      (fun phi => VanishesToInfiniteOrderOnCoincidence.one (onePointToFin1CLM d phi))
  have hInt (phi : SchwartzSpacetime d) :
      (∫ x : NPointDomain d 1, onePointToFin1CLM d phi x) = ∫ y : SpacetimeDim d, phi y := by
    change (∫ x : Fin 1 → SpacetimeDim d, phi (x 0)) = ∫ y : SpacetimeDim d, phi y
    exact MeasurePreserving.integral_comp'
      (volume_preserving_funUnique (Fin 1) (SpacetimeDim d)) (fun y => phi y)
  have hRight : Continuous (fun phi : SchwartzSpacetime d =>
      H.kernel 0 * ∫ x : NPointDomain d 1, onePointToFin1CLM d phi x) := by
    simp_rw [hInt]
    exact continuous_const.mul
      (SchwartzMap.integralCLM Complex (volume : Measure (SpacetimeDim d))).continuous
  have hpair (phi : SchwartzSpacetime d) :
      OS.S 1 (J phi) = H.kernel 0 * ∫ x : NPointDomain d 1, onePointToFin1CLM d phi x := by
    refine (SchwartzMap.dense_hasCompactSupport (m := d + 1)).induction ?_
      (isClosed_eq ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 1
        ).continuous.comp J.continuous) hRight) phi
    intro psi hpsi
    have h := H.compactChronological_wickIntegral_eq_schwinger Hstage Rstage (J psi)
      (hpsi.comp_homeomorph e.toHomeomorph) (fun _ _ j => Fin.elim0 j)
    have hzero (x : NPointDomain d 1) :
        H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal 1 d x j)) = H.kernel 0 :=
      congrArg H.kernel (Subsingleton.elim _ _)
    have h' : OS.S 1 (J psi) = ∫ x : NPointDomain d 1,
        H.kernel 0 * onePointToFin1CLM d psi x := by
      change OS.S 1 (J psi) = ∫ x : NPointDomain d 1, H.kernel 0 * (J psi).1 x
      simpa only [hzero] using h.symm
    exact h'.trans (MeasureTheory.integral_const_mul (H.kernel 0)
      (fun x : NPointDomain d 1 => onePointToFin1CLM d psi x))
  let phi := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm f.1
  have hJ : J phi = f := by
    apply Subtype.ext
    ext x
    change f.1 (e.symm (e x)) = f.1 x
    rw [e.symm_apply_apply]
  have hval : onePointToFin1CLM d phi = f.1 := congrArg Subtype.val hJ
  calc
    OS.S 1 f = H.kernel 0 * ∫ x : NPointDomain d 1, f.1 x := by
      simpa only [hJ, hval] using hpair phi
    _ = ∫ x : NPointDomain d 1, H.euclideanDensity x * f.1 x := by
      simp_rw [H.euclideanDensity_zeroGap_eq Hstage Rstage]
      exact (MeasureTheory.integral_const_mul (H.kernel 0)
        (fun x : NPointDomain d 1 => f.1 x)).symm

omit [NeZero k] in
theorem euclideanDensity_reproducesZeroDiagonal
    (H : OSIIReducedForwardTubeBoundaryData W)
    (lgc : OSLinearGrowthCondition d OS)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (f : ZeroDiagonalSchwartz d (k + 1)) :
    OS.S (k + 1) f = ∫ x : NPointDomain d (k + 1), H.euclideanDensity x * f.1 x := by
  by_cases hk : k = 0
  · subst k
    exact H.euclideanDensity_zeroGap_reproducesZeroDiagonal Hstage Rstage f
  · letI : NeZero k := ⟨hk⟩
    exact H.euclideanDensity_reproducesZeroDiagonal_of_pos lgc Hstage Rstage f

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedEuclideanDensity_reproducesZeroDiagonal
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (f : ZeroDiagonalSchwartz d (k + 1)) :
    OS.S (k + 1) f = ∫ x : NPointDomain d (k + 1),
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanDensity x * f.1 x :=
  (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k
    ).euclideanDensity_reproducesZeroDiagonal lgc
      (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
      (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) f

/-- The all-arity real Euclidean family, retaining the corrected input's
zero-point normalization and the native one-point scalar. -/
def strictGeneratedEuclideanKernel
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) : (n : Nat) -> NPointDomain d n -> Complex
  | 0 => fun _ => 1
  | k + 1 => (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).euclideanDensity

theorem strictGeneratedEuclideanKernel_reproducesZeroDiagonal
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat)
    (f : ZeroDiagonalSchwartz d n) :
    OS.S n f = ∫ x : NPointDomain d n, initial.strictGeneratedEuclideanKernel lgc n x * f.1 x := by
  cases n with
  | zero =>
      have hvol : (volume : Measure (NPointDomain d 0)) Set.univ = 1 := by
        rw [volume_pi]
        exact Measure.pi_empty_univ
          (μ := fun _ : Fin 0 => (volume : Measure (Fin (d + 1) -> Real)))
          (β := fun _ : Fin 0 => Fin (d + 1) -> Real)
      have hreal : (volume : Measure (NPointDomain d 0)).real Set.univ = 1 := by
        rw [Measure.real, hvol]
        norm_num
      rw [lgc.normalized_zero f]
      have hconst (x : NPointDomain d 0) : f.1 x = f.1 0 :=
        congrArg f.1 (Subsingleton.elim _ _)
      simp only [strictGeneratedEuclideanKernel, one_mul, hconst, integral_const, hreal]
      exact (one_smul Real (f.1 0)).symm
  | succ k =>
      exact initial.strictGeneratedEuclideanDensity_reproducesZeroDiagonal lgc k f

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
