import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledWard
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICoupledBoostFlow
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalTimeBoundary

/-!
# The boost Ward identity of the actual OS-II tempered boundary

Both the continuation and its boundary are the existing original-source
constructions. The empty zero-gap generator is handled separately.
-/

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d k : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

/-- The actual all-arity chronological boundary annihilates each
simultaneous boost generator, from precisely the corrected OS-II input. -/
theorem strictGeneratedTimeBoundary_boostDeriv_eq_zero
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (a : Fin d)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).timeSpatialBoundary
      (osiiCoupledBoostDeriv d k a Phi) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [osiiCoupledBoostDeriv_zero_arity, map_zero]
  letI : NeZero k := ⟨hk⟩
  exact (initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc k
    ).timeSpatialBoundary_boostDeriv_eq_zero
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k)
      (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
      a (fun _ => 1) (by intro j; norm_num) Phi

/-- The actual chronological boundary is invariant under every finite
coordinate boost, at every arity. -/
theorem strictGeneratedTimeBoundary_boost_eq
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (a : Fin d) (t : Real)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d k) Complex) :
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).timeSpatialBoundary
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiCoupledBoostCLE d k a t) Phi) =
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).timeSpatialBoundary Phi :=
  osiiCoupledBoost_pairing_eq a _
    (fun psi => initial.strictGeneratedTimeBoundary_boostDeriv_eq_zero lgc a psi) t Phi

/-- Finite boost covariance in the native reduced spacetime presentation,
with the same boundary distribution and no new choice of boundary. -/
theorem strictGeneratedReducedBoundary_boost_eq
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (a : Fin d) (t : Real)
    (f : SchwartzNPoint d k) :
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiNPointBoostCLE d k a t) f) =
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary f := by
  let C := nPointTimeSpatialSchwartzCLE (d := d) (n := k)
  have h := initial.strictGeneratedTimeBoundary_boost_eq lgc a t (C f)
  change (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
      (C.symm (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (osiiCoupledBoostCLE d k a t) (C f))) =
    (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
      (C.symm (C f)) at h
  rw [show SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (osiiCoupledBoostCLE d k a t) (C f) =
        C (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiNPointBoostCLE d k a t) f)
    from (nPointTimeSpatialSchwartzCLE_boost a t f).symm,
    C.symm_apply_apply, C.symm_apply_apply] at h
  exact h

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
