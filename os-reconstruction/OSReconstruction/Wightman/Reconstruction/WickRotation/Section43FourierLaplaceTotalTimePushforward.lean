/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Tietze











noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators Convolution Pointwise

namespace OSReconstruction

/-- Convolution of two one-dimensional compact strict-positive time sources.

The sum of two strict-positive time variables is strict-positive, and compact
support is preserved by convolution. -/
def section43CompactPositiveTimeSource1D_convolution
    (g h : Section43CompactPositiveTimeSource1D) :
    Section43CompactPositiveTimeSource1D := by
  let fconv : ℝ → ℂ :=
    (g.f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (h.f : ℝ → ℂ)
  have hconv_compact : HasCompactSupport fconv := by
    simpa [fconv] using
      (g.compact.convolution (L := ContinuousLinearMap.mul ℝ ℂ) h.compact)
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) fconv := by
    have hg_loc : LocallyIntegrable (g.f : ℝ → ℂ) volume := by
      exact (g.f.integrable (μ := volume)).locallyIntegrable
    simpa [fconv] using
      h.compact.contDiff_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℂ) hg_loc
        (h.f.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h.f : ℝ → ℂ))
  let convS : SchwartzMap ℝ ℂ := hconv_compact.toSchwartzMap hconv_smooth
  have hconv_eq : (convS : ℝ → ℂ) = fconv := by
    ext x
    simp [convS]
  refine ⟨convS, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ tsupport fconv := by
      simpa [hconv_eq] using hx
    have hsum_closed : IsClosed
        (tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ)) := by
      exact (g.compact.isCompact.add h.compact.isCompact).isClosed
    have htsupp_subset :
        tsupport fconv ⊆
          tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ) := by
      refine closure_minimal ?_ hsum_closed
      exact (support_convolution_subset
        (L := ContinuousLinearMap.mul ℝ ℂ)).trans
          (Set.add_subset_add subset_closure subset_closure)
    have hxsum :
        x ∈ tsupport (g.f : ℝ → ℂ) + tsupport (h.f : ℝ → ℂ) :=
      htsupp_subset hx'
    rcases hxsum with ⟨u, hu, v, hv, rfl⟩
    exact add_pos (Set.mem_Ioi.mp (g.positive hu)) (Set.mem_Ioi.mp (h.positive hv))
  · simpa [hconv_eq] using hconv_compact

/-- Concrete integral formula for the one-dimensional positive-time source
convolution. -/
theorem section43CompactPositiveTimeSource1D_convolution_apply
    (g h : Section43CompactPositiveTimeSource1D) (t : ℝ) :
    (section43CompactPositiveTimeSource1D_convolution g h).f t =
      ∫ s : ℝ, (g.f s) * h.f (t - s) := by
  simp [section43CompactPositiveTimeSource1D_convolution, convolution_def]

/-- Iterated convolution of a nonempty finite family of compact
strict-positive time sources. -/
def section43CompactPositiveTimeSource1D_totalConvolution :
    {n : ℕ} →
      (Fin (n + 1) → Section43CompactPositiveTimeSource1D) →
        Section43CompactPositiveTimeSource1D
  | 0, gs => gs 0
  | n + 1, gs =>
      section43CompactPositiveTimeSource1D_convolution
        (gs 0)
        (section43CompactPositiveTimeSource1D_totalConvolution
          (fun p : Fin (n + 1) => gs p.succ))

@[simp]
theorem section43CompactPositiveTimeSource1D_totalConvolution_zero
    (gs : Fin 1 → Section43CompactPositiveTimeSource1D) :
    section43CompactPositiveTimeSource1D_totalConvolution gs = gs 0 := rfl

@[simp]
theorem section43CompactPositiveTimeSource1D_totalConvolution_succ
    {n : ℕ}
    (gs : Fin (n + 2) → Section43CompactPositiveTimeSource1D) :
    section43CompactPositiveTimeSource1D_totalConvolution gs =
      section43CompactPositiveTimeSource1D_convolution
        (gs 0)
        (section43CompactPositiveTimeSource1D_totalConvolution
          (fun p : Fin (n + 1) => gs p.succ)) := rfl

end OSReconstruction
