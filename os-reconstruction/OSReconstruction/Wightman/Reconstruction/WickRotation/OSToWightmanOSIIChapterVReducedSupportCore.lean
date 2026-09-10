import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceWitness
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
import OSReconstruction.Wightman.SpectralEquivalence

/-!
# Chapter V Reduced Support Core

Low-level consecutive-time support definitions used by both the reduced
Schwinger construction and the ordered-product E-to-R route.  Keeping them
below the analytic Chapter V file prevents elementary support transport from
pulling in the boundary-value stack.
-/

open Set
open scoped Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

/-- Consecutive Euclidean time differences of an absolute configuration. -/
noncomputable def reducedTimeProjectionCLM
    (d m : ℕ) [NeZero d] :
    NPointDomain d (m + 1) →L[ℝ] (Fin m → ℝ) :=
  (section43QTimeCLM d m).comp
    (BHW.reducedDiffMapRealCLM (m + 1) d)

@[simp] theorem reducedTimeProjectionCLM_apply
    (x : NPointDomain d (m + 1)) :
    reducedTimeProjectionCLM d m x =
      section43QTime (d := d) (n := m)
        (BHW.reducedDiffMapReal (m + 1) d x) := by
  ext i
  rfl

omit [NeZero d] in
/-- The consecutive differences of the basepoint fiber section are exactly
the original reduced configuration. -/
theorem reducedDiffMapReal_diffVarSection
    (a : SpacetimeDim d)
    (ξ : NPointDomain d m) :
    BHW.reducedDiffMapReal (m + 1) d
        (fun k μ => a μ + diffVarSection d m ξ k μ) =
      ξ := by
  ext i μ
  rw [BHW.reducedDiffMapReal_apply]
  let j : Fin m := ⟨i.val, by omega⟩
  change
    (a μ + diffVarSection d m ξ j.succ μ) -
        (a μ + diffVarSection d m ξ j.castSucc μ) =
      ξ j μ
  rw [diffVarSection_succ]
  ring

/-- A source has compact strict-positive reduced-time support when its
consecutive time-gap projection is carried by one compact subset of the
strict-positive orthant.  No compactness in the common basepoint or spatial
variables is required. -/
def HasCompactStrictPositiveReducedTimeSupport
    (φ : SchwartzNPoint d (m + 1)) : Prop :=
  ∃ K : Set (Fin m → ℝ),
    IsCompact K ∧
      K ⊆ section43TimeStrictPositiveRegion m ∧
      ∀ x ∈ tsupport (φ : NPointDomain d (m + 1) → ℂ),
        reducedTimeProjectionCLM d m x ∈ K

end OSIIChapterV
end OSReconstruction
