import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeClustering
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeLocality
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeSpectralCondition
import OSReconstruction.Wightman.Reconstruction.WickRotation.WickRotationPairUniqueness

/-!
# Native E-to-R reconstruction

The existing distributional Wightman predicates and the full zero-diagonal
Wick pair hold for one native family. The family is unique even among all
candidates satisfying the literal Wick-pair contract.

The shared Wightman record states spectral support separately from analytic
boundary recovery. Its public assembly lives downstream in
`OSToWightmanReconstruction` to avoid a reverse import through legacy utilities.
-/

noncomputable section

open Complex

namespace OSReconstruction

theorem exists_osii_native_reconstruction
    {d : Nat} [NeZero d] (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ W : (n : Nat) -> SchwartzNPoint d n →L[Complex] Complex,
      IsWickRotationPair OS.schwinger (fun n f => W n f) ∧
      IsNormalized d (fun n f => W n f) ∧
      IsTranslationInvariantWeak d (fun n f => W n f) ∧
      IsLorentzCovariantWeak d (fun n f => W n f) ∧
      SpectralConditionDistribution d (fun n f => W n f) ∧
      ForwardTubeAnalyticityCompactSubset d (fun n f => W n f) ∧
      IsLocallyCommutativeWeak d (fun n f => W n f) ∧
      Wightman.IsPositiveDefinite d (fun n f => W n f) ∧
      (∀ n (f g : SchwartzNPoint d n),
        (∀ x, g x = starRingEnd Complex (f (fun i => x (Fin.rev i)))) ->
        W n g = starRingEnd Complex (W n f)) ∧
      (∀ F : BorchersSequence d, ∃ r : Real, 0 ≤ r ∧
        WightmanInnerProduct d (fun n f => W n f) F F = r) ∧
      (∀ n m (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (epsilon : Real),
        0 < epsilon -> ∃ R : Real, 0 < R ∧ ∀ a : SpacetimeDim d, a 0 = 0 ->
          (∑ i : Fin d, (a i.succ)^2) > R^2 -> ∀ ga : SchwartzNPoint d m,
            (∀ x, ga x = g (fun i => x i - a)) ->
            ‖W (n + m) (f.tensorProduct ga) - W n f * W m g‖ < epsilon) ∧
      (∀ V : (n : Nat) -> SchwartzNPoint d n -> Complex,
        IsWickRotationPair OS.schwinger V -> V = fun n f => W n f) := by
  obtain ⟨initial⟩ := OSIIChapterV.InitialGeneratedLogarithmicStageLevelData.exists_initial_ofOS OS
  refine ⟨initial.strictGeneratedFullBoundary lgc,
    initial.strictGenerated_isWickRotationPair lgc, (fun _ => rfl),
    initial.strictGeneratedFullBoundary_translationInvariant lgc,
    initial.strictGeneratedFullBoundary_lorentzCovariant lgc,
    initial.strictGeneratedFullBoundary_spectralCondition lgc,
    initial.strictGenerated_forwardTubeAnalyticityCompactSubset lgc,
    initial.strictGeneratedFullBoundary_locality lgc,
    initial.strictGeneratedFullBoundary_positive lgc,
    initial.strictGeneratedFullBoundary_hermitian lgc,
    initial.strictGeneratedFullBoundary_positive_real lgc,
    initial.strictGeneratedFullBoundary_cluster lgc, ?_⟩
  intro V hV
  exact wickRotationPair_unique hV (initial.strictGenerated_isWickRotationPair lgc)

end OSReconstruction
