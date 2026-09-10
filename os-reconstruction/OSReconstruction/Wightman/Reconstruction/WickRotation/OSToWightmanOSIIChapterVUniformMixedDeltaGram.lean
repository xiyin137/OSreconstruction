import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedHilbertGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDeltaHilbertLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeSmearingRealEdge

/-!
# OS-II Chapter V mixed Gram delta adapter

The common mixed Hilbert-field construction identifies every finite-scale
pairing with a pair-indexed scalar Cauchy continuation. The remaining
delta-source obligation is scalar: represent those continuations locally as
tensor smearings of one jointly continuous kernel.

This module performs the exact handoff. It deliberately leaves the local A0
kernel representation as an input rather than concealing it behind a new
analytic hypothesis.
-/

open Complex Filter Set Topology
open scoped Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

namespace UniformCompactTimeMixedHilbertGramFamilyData

/-- The selected pairwise Cauchy scalar is the underlying moving-slice
continuation at the reflected increment used by the Hilbert Gram identity. -/
theorem cauchy_scalar_at_reflectedIncrement
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (G : UniformCompactTimeMixedHilbertGramFamilyData
      OS f stage germ)
    (a b : ι)
    (w : Fin (q + 1) → ℂ) :
    (G.cauchy a b).scalar
        ((G.cauchy a b).center + reflectedCauchyIncrement w) =
      reflectedMovingSliceScalar stage germ.η
        (diffVarReduction d ((q + 1) + ((q + 1) + 1))
          (mixedReflectedChronologicalSource (f a).1 (f b).1))
        (reflectedCauchyIncrement w) := by
  rw [G.cauchy_scalar a b, G.cauchy_center a b, zero_add]

/-- A compact-local tensor-smearing representation of the pair-indexed scalar
Cauchy continuations supplies the producer contract for locally uniform
delta-field Gram convergence. -/
noncomputable def toLocallyCompactTensorPairGramRepresentationData
    {ι : Type*}
    {m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (G : UniformCompactTimeMixedHilbertGramFamilyData
      OS f stage germ)
    (sourceIndex : ℕ → ι)
    (U : Set (Fin (q + 1) → ℂ))
    (left right : SchwartzTimeApproximateIdentity m)
    (value : (Fin (q + 1) → ℂ) → ℂ)
    (localData :
      ∀ z ∈ U,
        ∃ K ∈ 𝓝[U] z, IsCompact K ∧
          (∀ w ∈ K, ‖w‖ < G.gramRadius) ∧
          ∃ R > 0,
            ∃ kernel :
                (Fin (q + 1) → ℂ) →
                  (Fin (m + m) → ℝ) → ℂ,
              ∃ center :
                  (Fin (q + 1) → ℂ) →
                    (Fin (m + m) → ℝ),
                ContinuousOn
                    (Function.uncurry fun w y =>
                      kernel w (center w + y))
                    (K ×ˢ
                      Metric.closedBall
                        (0 : Fin (m + m) → ℝ) R) ∧
                  (∀ (pq : ℕ × ℕ) w, w ∈ K →
                    MeasureTheory.Integrable
                      (fun y : Fin (m + m) → ℝ =>
                        ((left.test pq.1).tensorProduct
                          (right.test pq.2)) y *
                            kernel w (center w + y))) ∧
                  (∀ (pq : ℕ × ℕ) w, w ∈ K →
                    (G.cauchy
                        (sourceIndex pq.1)
                        (sourceIndex pq.2)).scalar
                      ((G.cauchy
                          (sourceIndex pq.1)
                          (sourceIndex pq.2)).center +
                        reflectedCauchyIncrement w) =
                      ∫ y : Fin (m + m) → ℝ,
                        ((left.test pq.1).tensorProduct
                          (right.test pq.2)) y *
                            kernel w (center w + y)) ∧
                  ∀ w ∈ K, value w = kernel w (center w)) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) m (OSHilbertSpace OS) _ _
      (fun N z => G.hilbert.field (sourceIndex N) z) U where
  leftTest := left.test
  rightTest := right.test
  leftRadius := left.radius
  rightRadius := right.radius
  left_nonnegative := left.nonnegative
  right_nonnegative := right.nonnegative
  left_real := left.real
  right_real := right.real
  left_integral_one := left.integral_one
  right_integral_one := right.integral_one
  left_support := left.support
  right_support := right.support
  leftRadius_tendsto := left.radius_tendsto
  rightRadius_tendsto := right.radius_tendsto
  value := value
  localData := by
    intro z hz
    obtain ⟨K, hK_nhds, hK_compact, hK_radius,
      R, hR, kernel, center, hcontinuous, hintegrable,
      hscalar, hvalue⟩ :=
      localData z hz
    refine
      ⟨K, hK_nhds, hK_compact, R, hR, kernel, center,
        hcontinuous, hintegrable, ?_, hvalue⟩
    intro pq w hw
    rw [G.mixed_inner
      (sourceIndex pq.1) (sourceIndex pq.2) w (hK_radius w hw)]
    exact hscalar pq w hw

/-- Source-facing form of the mixed delta adapter. It is enough to represent
the concrete moving-slice continuation as a local tensor smearing; the
selected Cauchy scalar is identified with that continuation automatically. -/
noncomputable def toLocallyCompactTensorPairGramRepresentationData_of_movingSlice
    {ι : Type*}
    {m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1))
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS f)
    (G : UniformCompactTimeMixedHilbertGramFamilyData
      OS f stage germ)
    (sourceIndex : ℕ → ι)
    (U : Set (Fin (q + 1) → ℂ))
    (left right : SchwartzTimeApproximateIdentity m)
    (value : (Fin (q + 1) → ℂ) → ℂ)
    (localData :
      ∀ z ∈ U,
        ∃ K ∈ 𝓝[U] z, IsCompact K ∧
          (∀ w ∈ K, ‖w‖ < G.gramRadius) ∧
          ∃ R > 0,
            ∃ kernel :
                (Fin (q + 1) → ℂ) →
                  (Fin (m + m) → ℝ) → ℂ,
              ∃ center :
                  (Fin (q + 1) → ℂ) →
                    (Fin (m + m) → ℝ),
                ContinuousOn
                    (Function.uncurry fun w y =>
                      kernel w (center w + y))
                    (K ×ˢ
                      Metric.closedBall
                        (0 : Fin (m + m) → ℝ) R) ∧
                  (∀ (pq : ℕ × ℕ) w, w ∈ K →
                    MeasureTheory.Integrable
                      (fun y : Fin (m + m) → ℝ =>
                        ((left.test pq.1).tensorProduct
                          (right.test pq.2)) y *
                            kernel w (center w + y))) ∧
                  (∀ (pq : ℕ × ℕ) w, w ∈ K →
                    reflectedMovingSliceScalar stage germ.η
                        (diffVarReduction d
                          ((q + 1) + ((q + 1) + 1))
                          (mixedReflectedChronologicalSource
                            (f (sourceIndex pq.1)).1
                            (f (sourceIndex pq.2)).1))
                        (reflectedCauchyIncrement w) =
                      ∫ y : Fin (m + m) → ℝ,
                        ((left.test pq.1).tensorProduct
                          (right.test pq.2)) y *
                            kernel w (center w + y)) ∧
                  ∀ w ∈ K, value w = kernel w (center w)) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) m (OSHilbertSpace OS) _ _
      (fun N z => G.hilbert.field (sourceIndex N) z) U :=
  G.toLocallyCompactTensorPairGramRepresentationData
    OS f stage germ sourceIndex U left right value (by
      intro z hz
      obtain ⟨K, hK_nhds, hK_compact, hK_radius,
        R, hR, kernel, center, hcontinuous, hintegrable,
        hmoving, hvalue⟩ :=
        localData z hz
      refine
        ⟨K, hK_nhds, hK_compact, hK_radius,
          R, hR, kernel, center, hcontinuous, hintegrable, ?_, hvalue⟩
      intro pq w hw
      rw [G.cauchy_scalar_at_reflectedIncrement
        OS f stage germ (sourceIndex pq.1) (sourceIndex pq.2) w]
      exact hmoving pq w hw)

end UniformCompactTimeMixedHilbertGramFamilyData

end OSIIChapterV
end OSReconstruction
