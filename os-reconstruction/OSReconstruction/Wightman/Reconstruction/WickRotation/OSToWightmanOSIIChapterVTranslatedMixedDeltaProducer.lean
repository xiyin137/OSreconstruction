/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedMixedMovingSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedDeltaGram









noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

namespace Section43ProductTimeApproximateIdentity

/-- The scalar selected by the translated mixed delta limit. -/
def mixedMovingKernelCenterValue
    (τ : Fin ((q + 1) + 1) → ℝ)
    (A : OSIITimeContinuationStage d ((q + 1) + ((q + 1) + 1)))
    (ρ : SchwartzMap (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (w : Fin (q + 1) → ℂ) : ℂ :=
  osiiReflectedMixedMovingKernel A ρ χ χ
    (reflectedCauchyIncrement w)
    (osiiMixedTimeCenter τ τ)

/-- The cutoff-weighted real-edge A0 value at the common left/right time
center. -/
def mixedMovingKernelCenterA0Value
    {ι : Type*}
    {f : ι → euclideanPositiveTimeSubmodule
      (d := d) ((q + 1) + 1)}
    (τ : Fin ((q + 1) + 1) → ℝ)
    (S : UniformCompactTimeMixedReflectedSourceStageData OS f)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) : ℂ :=
  let σ :=
    osiiMixedBlockGlobalReducedTime (q + 1)
      (osiiMixedTimeCenter τ τ)
  S.germ.η σ *
    S.edge.orbit σ
      (osiiMixedSpatialHeadMarginal χ χ)

/-- A tail of translated product-time delta sources satisfies the complete
compact-local pairwise Gram representation contract on the natural Gram
ball. -/
noncomputable def
    toLocallyCompactTensorPairGramRepresentationData_translated
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (N0 : ℕ)
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0)))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0))
      stage germ) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) ((q + 1) + 1) (OSHilbertSpace OS) _ _
      (fun N z => G.hilbert.field (N, χ) z)
      (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) := by
  let tail :=
    I.toSchwartzTimeApproximateIdentity.tail N0
  exact
    G.toLocallyCompactTensorPairGramRepresentationData_of_movingSlice
      OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0))
      stage germ
      (fun N => (N, χ))
      (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius)
      tail tail
      (mixedMovingKernelCenterValue τ stage germ.η χ)
      (by
        intro z hz
        have hz_norm : ‖z‖ < G.gramRadius := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        let r : ℝ := (‖z‖ + G.gramRadius) / 2
        have hzr : ‖z‖ < r := by
          dsimp [r]
          linarith
        have hrG : r < G.gramRadius := by
          dsimp [r]
          linarith
        let K : Set (Fin (q + 1) → ℂ) :=
          Metric.closedBall 0 r
        have hK_nhds :
            K ∈ 𝓝[Metric.ball
              (0 : Fin (q + 1) → ℂ) G.gramRadius] z := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Metric.closedBall_mem_nhds_of_mem
          simpa [K, Metric.mem_ball, dist_zero_right] using hzr
        have hK_compact : IsCompact K := by
          exact isCompact_closedBall 0 r
        have hK_radius :
            ∀ w ∈ K, ‖w‖ < G.gramRadius := by
          intro w hw
          have hw_le : ‖w‖ ≤ r := by
            simpa [K, Metric.mem_closedBall, dist_zero_right] using hw
          exact hw_le.trans_lt hrG
        refine
          ⟨K, hK_nhds, hK_compact, hK_radius,
            1, zero_lt_one, ?_, ?_, ?_⟩
        · exact fun w y =>
            osiiReflectedMixedMovingKernel
              stage germ.η χ χ
              (reflectedCauchyIncrement w) y
        · exact fun _ => osiiMixedTimeCenter τ τ
        · refine ⟨?_, ?_, ?_, ?_⟩
          · intro p hp
            exact
              (continuousAt_osiiReflectedMixedMovingKernel_cauchyShift
                stage germ.η χ χ
                (G.gram_carrier p.1 (hK_radius p.1 hp.1))
                (osiiMixedTimeCenter τ τ) p.2).continuousWithinAt
          · intro pq w hw
            exact
              integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
                stage germ.η χ χ
                (I.test (pq.1 + N0)) (I.test (pq.2 + N0))
                (I.test_compact (pq.1 + N0))
                (I.test_compact (pq.2 + N0))
                (G.gram_carrier w (hK_radius w hw))
                (osiiMixedTimeCenter τ τ)
          · intro pq w hw
            exact
              reflectedMovingSliceScalar_translatedApproximateIdentities
                stage germ.η I I τ τ hτ hτ χ χ
                (pq.1 + N0) (pq.2 + N0)
                (reflectedCauchyIncrement w)
                (G.gram_carrier w (hK_radius w hw))
          · intro w hw
            rfl)

/-- The concrete translated-source producer supplies the locally uniform
pairwise Gram limit data used by Hilbert-field completion. -/
noncomputable def toLocallyUniformPairwiseInnerLimitData_translated
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (N0 : ℕ)
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0)))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0))
      stage germ) :
    LocallyUniformPairwiseInnerLimitData
      (fun N z => G.hilbert.field (N, χ) z)
      (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) :=
  (I.toLocallyCompactTensorPairGramRepresentationData_translated
    OS τ hτ χ N0 stage germ G).toLocallyUniformPairwiseInnerLimitData

/-- The translated shrinking-time Hilbert fields have a locally uniform
holomorphic limit on the natural Gram ball. -/
theorem exists_translatedHolomorphicHilbertField
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (N0 : ℕ)
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0)))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + N0))
      stage germ) :
    ∃ Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS,
      TendstoLocallyUniformlyOn
          (fun N z => G.hilbert.field (N, χ) z)
          Ψ atTop
          (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) ∧
        DifferentiableOn ℂ Ψ
          (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) := by
  apply
    (I.toLocallyUniformPairwiseInnerLimitData_translated
      OS τ hτ χ N0 stage germ G).exists_holomorphicField
  · intro N
    apply (G.hilbert.holomorphic (N, χ)).mono
    intro z hz
    have hz_norm : ‖z‖ < G.gramRadius := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    intro i
    have hzi : ‖z i‖ < G.hilbert.radius :=
      (norm_le_pi_norm z i).trans_lt
        (hz_norm.trans G.gramRadius_lt_hilbert)
    simpa [dist_zero_right] using hzi
  · exact Metric.isOpen_ball

end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
