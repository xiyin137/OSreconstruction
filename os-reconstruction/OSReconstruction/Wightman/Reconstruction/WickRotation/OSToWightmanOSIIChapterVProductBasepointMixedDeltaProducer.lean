/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPositiveProductBasepointFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorExhaustion
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedDelta
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformMixedDeltaGram










noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}

/-- The scalar selected by the internal-gap delta limit for an anchored
product-basepoint source. -/
def productBasepointMixedKernelCenterValue
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (ρ : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (q + 1)) ℂ)
    (w : Fin (q + 1) → ℂ) : ℂ :=
  osiiReflectedMixedProductBasepointKernel
    stage ρ
    normalizedPositiveTimeBasepointCutoff.f
    normalizedPositiveTimeBasepointCutoff.f
    (section43SpatialBasepointLiftCLM d (q + 1)
      (normalizedSpatialBasepointCutoff d).toSchwartz χ)
    (section43SpatialBasepointLiftCLM d (q + 1)
      (normalizedSpatialBasepointCutoff d).toSchwartz χ)
    (reflectedCauchyIncrement w)
    (Fin.append anchor anchor)

/-- The anchored product-basepoint source family satisfies the complete
compact-local pairwise Gram representation contract on its natural Gram
ball. -/
noncomputable def
    toLocallyCompactTensorPairGramRepresentationData_productBasepoint
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (χ : SchwartzMap
      (Section43SpatialSpace d (q + 1)) ℂ)
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ :
      UniformCompactTimeMixedReflectedSourceFamilyData OS
        (fun p :
            ℕ × SchwartzMap
              (Section43SpatialSpace d (q + 1)) ℂ =>
          A.positiveProductBasepointSource p.1 p.2))
    (G :
      UniformCompactTimeMixedHilbertGramFamilyData OS
        (fun p :
            ℕ × SchwartzMap
              (Section43SpatialSpace d (q + 1)) ℂ =>
          A.positiveProductBasepointSource p.1 p.2)
        stage germ) :
    @LocallyCompactTensorPairGramRepresentationData
      (q + 1) (q + 1) (OSHilbertSpace OS) _ _
      (fun N z => G.hilbert.field (N, χ) z)
      (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius) := by
  let tail :=
    I.toSchwartzTimeApproximateIdentity.tail
      A.carrierData.tailStart
  let θ : SchwartzMap ℝ ℂ :=
    normalizedPositiveTimeBasepointCutoff.f
  let ξ :
      SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ :=
    section43SpatialBasepointLiftCLM d (q + 1)
      (normalizedSpatialBasepointCutoff d).toSchwartz χ
  exact
    G.toLocallyCompactTensorPairGramRepresentationData_of_movingSlice
      OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d (q + 1)) ℂ =>
        A.positiveProductBasepointSource p.1 p.2)
      stage germ
      (fun N => (N, χ))
      (Metric.ball (0 : Fin (q + 1) → ℂ) G.gramRadius)
      tail tail
      (productBasepointMixedKernelCenterValue
        (anchor := anchor) stage germ.η χ)
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
        have hK_compact : IsCompact K :=
          isCompact_closedBall 0 r
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
            osiiReflectedMixedProductBasepointKernel
              stage germ.η θ θ ξ ξ
              (reflectedCauchyIncrement w) y
        · exact fun _ => Fin.append anchor anchor
        · refine ⟨?_, ?_, ?_, ?_⟩
          · intro p hp
            exact
              (continuousAt_osiiReflectedMixedProductBasepointKernel_cauchyShift
                stage germ.η germ.η_compact
                θ θ
                normalizedPositiveTimeBasepointCutoff.compact
                normalizedPositiveTimeBasepointCutoff.compact
                ξ ξ
                (G.gram_carrier p.1 (hK_radius p.1 hp.1))
                (Fin.append anchor anchor) p.2).continuousWithinAt
          · intro pq w hw
            exact
              integrable_tensorProduct_mul_osiiReflectedMixedProductBasepointKernel
                stage germ.η θ θ
                normalizedPositiveTimeBasepointCutoff.compact
                normalizedPositiveTimeBasepointCutoff.compact
                ξ ξ
                (tail.test pq.1) (tail.test pq.2)
                (tail.compact pq.1) (tail.compact pq.2)
                (G.gram_carrier w (hK_radius w hw))
                (Fin.append anchor anchor)
          · intro pq w hw
            rw [A.positiveProductBasepointSource_coe,
              A.positiveProductBasepointSource_coe]
            simpa [tail, θ, ξ, timeTest,
              SchwartzTimeApproximateIdentity.tail] using
              (reflectedMovingSliceScalar_productBasepoint_translatedApproximateIdentities
                stage germ.η θ θ tail tail anchor anchor χ χ
                normalizedPositiveTimeBasepointCutoff.compact
                normalizedPositiveTimeBasepointCutoff.compact
                pq.1 pq.2 w
                (G.gram_carrier w (hK_radius w hw)))
          · intro w hw
            rfl)

/-- At each shrinking time scale, the product-basepoint construction is a
continuous linear map from the reduced spatial Schwartz space to the OS
Hilbert space. -/
noncomputable def positiveProductBasepointVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d (q + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)).comp
    ((section43PositiveTimeSpatialSourceCLM d ((q + 1) + 1)
      (A.positiveProductBasepointTimeSource N)).comp
        (section43SpatialBasepointLiftCLM d (q + 1)
          (normalizedSpatialBasepointCutoff d).toSchwartz))

@[simp]
theorem positiveProductBasepointVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d (q + 1)) ℂ) :
    A.positiveProductBasepointVectorCLM OS N χ =
      osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
        (A.positiveProductBasepointSource N χ) :=
  rfl

/-- The scalar selected by the internal-gap delta limit when the fixed
positive head is paired with an arbitrary full spatial block. -/
def positiveHeadSpatialMixedKernelCenterValue
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (ρ : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) ℂ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (w : Fin (q + 1) → ℂ) : ℂ :=
  osiiReflectedMixedProductBasepointKernel
    stage ρ
    normalizedPositiveTimeBasepointCutoff.f
    normalizedPositiveTimeBasepointCutoff.f
    χ χ
    (reflectedCauchyIncrement w)
    (Fin.append anchor anchor)

/-- At each shrinking time scale, the arbitrary-full-spatial fixed-head
construction is a continuous linear map into the OS Hilbert space. -/
noncomputable def positiveHeadSpatialVectorCLM
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)).comp
    (section43PositiveTimeSpatialSourceCLM d ((q + 1) + 1)
      (A.positiveProductBasepointTimeSource N))

@[simp]
theorem positiveHeadSpatialVectorCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    A.positiveHeadSpatialVectorCLM OS N χ =
      osiiPositiveTimeSingleVectorCLM OS ((q + 1) + 1)
        (A.positiveHeadSpatialSource N χ) :=
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
