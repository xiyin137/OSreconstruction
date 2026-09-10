import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISameWitnessWickPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison

/-!
# Covariance of the full native boundary

The same Wick kernel supplies real translation and Lorentz covariance of
the absolute-coordinate distributions. Only the proved boundary limits and
the existing change-of-variables lemmas enter this handoff.
-/

noncomputable section

open Complex MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedFullBoundary_translationInvariant
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (fun n f => initial.strictGeneratedFullBoundary lgc n f) := by
  intro n
  apply bv_translation_invariance_transfer n
    (initial.strictGeneratedFullBoundary lgc n) (initial.strictGeneratedWickKernel lgc n)
    (initial.strictGeneratedWickKernel_boundaryValue lgc n)
  intro a x eta epsilon _
  have h := initial.strictGeneratedWickKernel_translate lgc n
    (fun j mu => (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I)
    (fun mu => -(a mu : Complex))
  change initial.strictGeneratedWickKernel lgc n
      (fun j mu => (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I +
        -(a mu : Complex)) = _ at h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

theorem strictGeneratedWickKernel_lorentz
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) (L : LorentzGroup d)
    (z : Fin n -> Fin (d + 1) -> Complex) (hz : z ∈ ForwardTube d n) :
    initial.strictGeneratedWickKernel lgc n
        (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup L)) z) =
      initial.strictGeneratedWickKernel lgc n z := by
  cases n with
  | zero => rfl
  | succ k =>
      let H := initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k
      have hLz : BHW.complexLorentzAction
          (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup L)) z ∈ ForwardTube d (k + 1) := by
        exact orthochronous_preserves_forward_tube L (LorentzGroup.zero_zero_ge_one L) z hz
      change H.wickPairKernel _ = H.wickPairKernel z
      rw [H.wickPairKernel_eqOn_forwardTube hLz, H.wickPairKernel_eqOn_forwardTube hz]
      change H.kernel (BHW.reducedDiffMap (k + 1) d
          (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup L)) z)) =
        H.kernel (BHW.reducedDiffMap (k + 1) d z)
      rw [BHW.reducedDiffMap_action]
      exact initial.strictGeneratedForwardTube_realLorentzInvariant lgc k
        (wightmanToLorentzGroup L) _
        ((BHW.mem_forwardTube_iff_basepoint_and_reducedDiff z).mp
          (by simpa only [BHW_forwardTube_eq] using hz)).2

theorem strictGeneratedFullBoundary_lorentzCovariant
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (fun n f => initial.strictGeneratedFullBoundary lgc n f) := by
  intro n L
  apply bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance n
    (initial.strictGeneratedFullBoundary lgc n) (initial.strictGeneratedWickKernel lgc n)
    (initial.strictGeneratedWickKernel_boundaryValue lgc n) ?_ L (LorentzGroup.zero_zero_ge_one L)
  intro L _ x epsilon hepsilon
  exact initial.strictGeneratedWickKernel_lorentz lgc n L _
    (by simpa only [forwardTube_eq_imPreimage] using
      (show (fun j mu => (x j mu : Complex) +
          (epsilon : Complex) * (canonicalForwardConeDirection (d := d) n j mu : Complex) * I) ∈
          TubeDomainSetPi (ForwardConeAbs d n) from by
        simpa [TubeDomainSetPi, Pi.smul_apply] using
          forwardConeAbs_smul d n epsilon hepsilon
            (canonicalForwardConeDirection (d := d) n) (canonicalForwardConeDirection_mem n)))

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
