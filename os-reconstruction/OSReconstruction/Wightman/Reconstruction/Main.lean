import OSReconstruction.Specification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReconstruction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeEndpoint
import OSReconstruction.Wightman.Reconstruction.WickRotation.RToEReconstruction

/-!
# OS reconstruction theorems

Distributional E'-to-R', its qualitative corollary, and full R-to-E.
Definitions and proof-independent target propositions are in `Specification`.
The operator/GNS reconstruction and uniqueness development is outside this package.
-/

noncomputable section
variable {d : ℕ} [NeZero d]

/-- The original continuous-linear reverse compatibility bridge. -/
theorem wightman_to_os (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W :=
  wightman_to_os_full Wfn

/-- Qualitative E'-to-R with locality, clustering, and spectral support. -/
theorem os_to_wightman (OS : OsterwalderSchraderAxioms d)
    (linear_growth : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.schwinger Wfn.W :=
  os_to_wightman_full OS linear_growth

/-- The public forward theorem inhabits the separate specification. -/
theorem OSReconstruction.e_to_r_specification {d : Nat} [NeZero d] :
    OSReconstruction.EToRStatement d :=
  fun OS lgc => os_to_wightman OS lgc

/-- The original-coordinate OS II theorem inhabits the separate specification. -/
theorem OSReconstruction.e_to_r_osii_specification {d : Nat} [NeZero d] :
    OSReconstruction.EToROSIIStatement d :=
  fun OS lgc => os_to_wightman_osii_original OS lgc

/-- The reverse theorem includes the literal constructor identity. -/
theorem OSReconstruction.r_to_e_specification {d : Nat} [NeZero d] :
    OSReconstruction.RToEStatement d constructSchwingerFunctions :=
  fun Wfn => OSReconstruction.wightman_to_os_axioms Wfn

end
