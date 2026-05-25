import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSelectedWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced

/-!
# Selected Reduced Input Bridge

This file keeps the small identification between the selected Route-1 reduced
input and the public reduced witness `bvt_F_reduced` out of the larger
frontier files.  It is a neutral bridge: it does not construct the missing
reduced PET/Ruelle extension, but it ensures that such an extension can be
used by the existing reduced pointwise boundary theorem without a naming shim.
-/

open scoped Classical NNReal

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The selected reduced Route-1 input is exactly the public reduced witness
`bvt_F_reduced`. -/
theorem bvt_selectedReducedForwardTubeInput_toFun_eq_bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    (bvt_selectedReducedForwardTubeInput (d := d) OS lgc χ m).toFun =
      bvt_F_reduced (d := d) OS lgc m := by
  funext η
  simp [bvt_selectedReducedForwardTubeInput, bvt_F_reduced,
    BHW.descendAbsoluteForwardTubeInput, bvt_absoluteForwardTubeInput]

/-- Any reduced PET extension of the selected input is a reduced PET extension
of the public reduced witness. -/
def bvt_F_reduced_extension_of_selected_input_extension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_selectedReducedForwardTubeInput (d := d) OS lgc χ m).toFun) :
    BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m) where
  toFun := Fred.toFun
  holomorphic := Fred.holomorphic
  agrees_on_reducedForwardTube := by
    intro η hη
    have h := Fred.agrees_on_reducedForwardTube η hη
    have heq :=
      congrFun
        (bvt_selectedReducedForwardTubeInput_toFun_eq_bvt_F_reduced
          (d := d) OS lgc χ m) η
    simpa [heq] using h
  lorentz_invariant := Fred.lorentz_invariant
  perm_invariant := Fred.perm_invariant

/-- Pointwise reduced two-direction boundary convergence from a genuine PET
extension of the selected reduced input. -/
theorem bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_selected_input_extension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_selectedReducedForwardTubeInput (d := d) OS lgc χ m).toFun)
    (ξ : NPointDomain d m)
    (hξ_pet :
      (fun k μ => (ξ k μ : ℂ)) ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  exact
    bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension
      (d := d) OS lgc m i j
      (bvt_F_reduced_extension_of_selected_input_extension
        (d := d) OS lgc χ m Fred)
      ξ hξ_pet

end OSReconstruction
