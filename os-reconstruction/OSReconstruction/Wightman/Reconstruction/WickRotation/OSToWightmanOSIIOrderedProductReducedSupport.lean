/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductSourceNormalization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSupportCore










noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- Compact absolute support projects to topological support of its
difference-variable fiber reduction. -/
theorem diffVarReduction_tsupport_subset_reducedDiff_image_tsupport_of_compact
    (f : SchwartzNPoint d (k + 1))
    (hf : HasCompactSupport
      (f : NPointDomain d (k + 1) → ℂ)) :
    tsupport
        ((diffVarReduction d k f : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) ⊆
      BHW.reducedDiffMapRealCLM (k + 1) d ''
        tsupport (f : NPointDomain d (k + 1) → ℂ) := by
  let K : Set (NPointDomain d k) :=
    BHW.reducedDiffMapRealCLM (k + 1) d ''
      tsupport (f : NPointDomain d (k + 1) → ℂ)
  have hK_compact : IsCompact K := by
    exact hf.isCompact.image
      (BHW.reducedDiffMapRealCLM (k + 1) d).continuous
  have hf_support_to_K :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (k + 1) d x ∈ K := by
    intro x hx
    exact ⟨x, subset_tsupport _ hx, rfl⟩
  have hsupport :
      Function.support
          ((diffVarReduction d k f : SchwartzNPoint d k) :
            NPointDomain d k → ℂ) ⊆ K := by
    intro ξ hξ
    by_contra hξK
    have hzero :
        ∀ a : SpacetimeDim d,
          f (fun j μ => a μ + diffVarSection d k ξ j μ) = 0 := by
      intro a
      by_contra ha
      apply hξK
      refine ⟨fun j μ => a μ + diffVarSection d k ξ j μ,
        subset_tsupport _ ha, ?_⟩
      simpa [BHW.reducedDiffMapRealCLM] using
        (OSIIChapterV.reducedDiffMapReal_diffVarSection
          (d := d) (m := k) a ξ)
    apply hξ
    change
      (∫ a : SpacetimeDim d,
        f (fun j μ => a μ + diffVarSection d k ξ j μ)) = 0
    simp_rw [hzero]
    simp
  rw [tsupport]
  apply closure_minimal
  · exact hsupport
  · exact hK_compact.isClosed

namespace OSIIOrderedCompactProductSource.PositiveNormalization

end OSIIOrderedCompactProductSource.PositiveNormalization

end OSReconstruction
