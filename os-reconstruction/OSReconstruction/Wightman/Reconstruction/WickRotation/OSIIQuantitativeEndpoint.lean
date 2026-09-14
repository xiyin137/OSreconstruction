import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeReconstruction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIOriginalGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReconstruction

/-!
# OS II reconstruction including R0'

The additional conclusion is proved for the existing native family and, by
the already-proved Wick-pair uniqueness, for the existing public constructor.
Neither the OS input nor the ordinary Wightman record is strengthened.
-/

noncomputable section

namespace OSReconstruction

theorem OSIIChapterV.InitialGeneratedLogarithmicStageLevelData.strictGeneratedFullBoundary_osii_growth
    {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}
    (initial : OSIIChapterV.InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIWightmanGrowthCondition d (fun n f => initial.strictGeneratedFullBoundary lgc n f) :=
  osiiWightmanGrowthCondition_of_uniformSchwartzBound
    (initial.exists_strictGeneratedUniformSchwartzBound lgc)

/-- R0' holds for every family satisfying the same Wick-pair contract with
these OS data, hence does not depend on a new choice of reconstruction. -/
theorem wickRotationPair_osii_growth
    {d : Nat} [NeZero d] (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {W : (n : Nat) -> SchwartzNPoint d n -> Complex}
    (hW : IsWickRotationPair OS.schwinger W) : OSIIWightmanGrowthCondition d W := by
  obtain ⟨initial⟩ := OSIIChapterV.InitialGeneratedLogarithmicStageLevelData.exists_initial_ofOS OS
  have heq := wickRotationPair_unique hW (initial.strictGenerated_isWickRotationPair lgc)
  rw [heq]
  exact initial.strictGeneratedFullBoundary_osii_growth lgc

end OSReconstruction

variable {d : Nat} [NeZero d]

/-- The literal preexisting public constructor satisfies OS II equation (4.3). -/
theorem constructWightmanFunctions_osii_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    OSReconstruction.OSIIWightmanGrowthCondition d (constructWightmanFunctions OS lgc).W :=
  OSReconstruction.wickRotationPair_osii_growth OS lgc
    (constructWightmanFunctions_isWickRotationPair OS lgc)

/-- OS II E'-to-R': all distributional Wightman axioms, full Euclidean
recovery, the uniform coordinate-norm estimate R0', and family uniqueness. -/
theorem os_to_wightman_osii (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ Wfn : WightmanFunctions d,
      IsWickRotationPair OS.schwinger Wfn.W ∧
      OSReconstruction.OSIIWightmanGrowthCondition d Wfn.W ∧
      ∀ V : (n : Nat) -> SchwartzNPoint d n -> Complex,
        IsWickRotationPair OS.schwinger V -> V = Wfn.W := by
  obtain ⟨Wfn, hpair⟩ := os_to_wightman_full OS lgc
  exact ⟨Wfn, hpair, OSReconstruction.wickRotationPair_osii_growth OS lgc hpair,
    fun _ hV => OSReconstruction.wickRotationPair_unique hV hpair⟩

/-- The same full OS II result with E0' written literally in the paper's
factorial-only coordinate-seminorm convention. -/
theorem os_to_wightman_osii_original (OS : OsterwalderSchraderAxioms d)
    (lgc : OSReconstruction.OSIIOriginalLinearGrowthCondition d OS) :
    ∃ Wfn : WightmanFunctions d,
      IsWickRotationPair OS.schwinger Wfn.W ∧
      OSReconstruction.OSIIWightmanGrowthCondition d Wfn.W ∧
      ∀ V : (n : Nat) -> SchwartzNPoint d n -> Complex,
        IsWickRotationPair OS.schwinger V -> V = Wfn.W :=
  os_to_wightman_osii OS lgc.toArityLinearGrowthCondition

end
