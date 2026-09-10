/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPositiveSourceSeminorm
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMZApproximation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockTranslation

/-!
# OS II Chapter VI: Uniform selected-block MZ bounds

This module supplies the scale estimate needed to use the selected-block
Malgrange-Zerner extension in the shrinking radial family.  It first
transports the full radial-source seminorm estimate through the selected
left/right block geometry.  The final step controls the packet's rotated
Hilbert vectors uniformly in the axis-pair direction and slope.
-/

noncomputable section

open Complex Matrix Metric Set
open scoped Classical

namespace OSReconstruction

theorem norm_osiiStep4SelectedRealBlock_le
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) :
    norm (osiiStep4SelectedRealBlock n m q x) <= norm x := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro mu
  simpa [osiiStep4SelectedRealBlock, Real.norm_eq_abs] using
    (norm_le_pi_norm x
      (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu)))

theorem norm_osiiStep4SelectedRealBlockHalf_le
    (n m q : Nat)
    (x : Fin ((n + 1 + m) * q) -> Real) :
    norm (osiiStep4SelectedRealBlockHalf n m q x) <= norm x := by
  rw [osiiStep4SelectedRealBlockHalf, norm_smul, Real.norm_eq_abs]
  norm_num
  have hselected := norm_osiiStep4SelectedRealBlock_le n m q x
  nlinarith [norm_nonneg x,
    norm_nonneg (osiiStep4SelectedRealBlock n m q x)]

theorem norm_selectedBlockLeftEndpointCenter_le
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    norm (osiiStep4SelectedBlockLeftEndpointCenter d n m center) <=
      norm center := by
  rw [osiiStep4SelectedBlockLeftEndpointCenter, norm_parity_eq]
  exact norm_osiiStep4SelectedRealBlockHalf_le n m (d + 1) center

theorem norm_selectedBlockRightEndpointCenter_le
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real) :
    norm (osiiStep4SelectedBlockRightEndpointCenter d n m center) <=
      norm center := by
  exact norm_osiiStep4SelectedRealBlockHalf_le n m (d + 1) center

set_option maxHeartbeats 800000 in
/-- Every finite seminorm family of the selected left source has one
inverse-radius exponent and one global-center growth degree. -/
theorem exists_selectedBlockLeftPositiveTimeSource_finsetSeminorm_scale_bound
    (d n m : Nat) [NeZero d] (t : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center : Fin ((n + 1 + m) * (d + 1)) -> Real),
          ∀ hcenter : ∀ i : Fin (n + 1 + m),
            rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))),
              ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) (n + 1 + m) rho,
                t.sup (schwartzSeminormFamily Real
                    (NPointDomain d (n + 1)) Complex)
                    (osiiStep4SelectedBlockLeftPositiveTimeSource
                      d n m hrho center p.1 p.2 hcenter).1 <=
                  C * (16 / rho) ^ M * (1 + norm center) ^ N := by
  obtain ⟨C, M, NEndpoint, NTail, hC, hbound⟩ :=
    exists_osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_finsetSeminorm_scale_bound
      d n t
  refine ⟨C, M, NEndpoint + NTail, hC, ?_⟩
  intro rho hrho hrho_le center hcenter p hp
  let endpointCenter :=
    osiiStep4SelectedBlockLeftEndpointCenter d n m center
  let endpointImag :=
    osiiStep4SelectedBlockLeftEndpointImag d n m p.1 p.2
  let centerL := osiiStep4ParityReversedBeforeRealBlocks d n m center
  let yL := osiiStep4ParityReversedBeforeRealBlocks d n m p.1
  let yL' := osiiStep4ParityReversedBeforeRealBlocks d n m p.2
  have hy : norm p.1 <= rho / 4 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp.1
  have hy' : norm p.2 <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp.2
  by_cases hEndpointImag : norm endpointImag <= rho / 8
  · have hEndpointImagMem :
        endpointImag ∈ Metric.closedBall 0 (rho / 8) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hEndpointImag
    have hpL : (yL, yL') ∈
        osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) n rho := by
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_parityReversedBefore_le d n m p.1).trans hy
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_parityReversedBefore_le d n m p.2).trans hy'
    have hradial := hbound hrho hrho_le endpointCenter endpointImag
      hEndpointImagMem centerL (yL, yL') hpL
    have hEndpointCenterNorm : norm endpointCenter <= norm center := by
      simpa [endpointCenter] using
        norm_selectedBlockLeftEndpointCenter_le d n m center
    have hcenterLNorm : norm centerL <= norm center := by
      simpa [centerL] using norm_parityReversedBefore_le d n m center
    have hbase : 0 <= 1 + norm center := by positivity
    change t.sup (schwartzSeminormFamily Real
        (NPointDomain d (n + 1)) Complex)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d n hrho endpointCenter endpointImag centerL yL yL') <= _
    calc
      t.sup (schwartzSeminormFamily Real
          (NPointDomain d (n + 1)) Complex)
          (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
            d n hrho endpointCenter endpointImag centerL yL yL') <=
        C * (16 / rho) ^ M *
          (1 + norm endpointCenter) ^ NEndpoint *
          (1 + norm centerL) ^ NTail := hradial
      _ <= C * (16 / rho) ^ M *
          (1 + norm center) ^ NEndpoint *
          (1 + norm center) ^ NTail := by
        gcongr
      _ = C * (16 / rho) ^ M *
          (1 + norm center) ^ (NEndpoint + NTail) := by
        rw [pow_add]
        ring
  · have hEndpointImag' : rho / 8 < norm endpointImag :=
      lt_of_not_ge hEndpointImag
    have hsourceZero :
        osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d n hrho endpointCenter endpointImag centerL yL yL' = 0 :=
      radialEndpointSource_eq_zero_of_imag_norm_gt
        d n hrho endpointCenter endpointImag centerL yL yL' hEndpointImag'
    change t.sup (schwartzSeminormFamily Real
        (NPointDomain d (n + 1)) Complex)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d n hrho endpointCenter endpointImag centerL yL yL') <= _
    rw [hsourceZero]
    simp
    positivity

set_option maxHeartbeats 800000 in
/-- Every finite seminorm family of the selected right source has the
corresponding inverse-radius and global-center estimate. -/
theorem exists_selectedBlockRightPositiveTimeSource_finsetSeminorm_scale_bound
    (d n m : Nat) [NeZero d] (t : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center : Fin ((n + 1 + m) * (d + 1)) -> Real),
          ∀ hcenter : ∀ i : Fin (n + 1 + m),
            rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))),
              ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) (n + 1 + m) rho,
                t.sup (schwartzSeminormFamily Real
                    (NPointDomain d (m + 1)) Complex)
                    (osiiStep4SelectedBlockRightPositiveTimeSource
                      d n m hrho center p.1 p.2 hcenter).1 <=
                  C * (16 / rho) ^ M * (1 + norm center) ^ N := by
  obtain ⟨C, M, NEndpoint, NTail, hC, hbound⟩ :=
    exists_osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_finsetSeminorm_scale_bound
      d m t
  refine ⟨C, M, NEndpoint + NTail, hC, ?_⟩
  intro rho hrho hrho_le center hcenter p hp
  let endpointCenter :=
    osiiStep4SelectedBlockRightEndpointCenter d n m center
  let endpointImag :=
    osiiStep4SelectedBlockRightEndpointImag d n m p.2
  let centerR := osiiStep4AfterRealBlocks n m (d + 1) center
  let yR := osiiStep4AfterRealBlocks n m (d + 1) p.1
  let yR' := osiiStep4AfterRealBlocks n m (d + 1) p.2
  have hy : norm p.1 <= rho / 4 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp.1
  have hy' : norm p.2 <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp.2
  have hpR : (yR, yR') ∈
      osiiStep4PartialConvolutionClosedImaginaryBox (d + 1) m rho := by
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_afterBlocks_le n m (d + 1) p.1).trans hy
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_afterBlocks_le n m (d + 1) p.2).trans hy'
  have hEndpointImag : norm endpointImag <= rho / 8 := by
    apply le_trans _ hy'
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg p.2)]
    intro mu
    simpa [endpointImag, osiiStep4SelectedBlockRightEndpointImag,
      osiiStep4SelectedRealBlock] using
      (norm_le_pi_norm p.2
        (finProdFinEquiv (osiiStep4SelectedBlockIndex n m, mu)))
  have hEndpointImagMem :
      endpointImag ∈ Metric.closedBall 0 (rho / 8) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hEndpointImag
  have hradial := hbound hrho hrho_le endpointCenter endpointImag
    hEndpointImagMem centerR (yR, yR') hpR
  have hEndpointCenterNorm : norm endpointCenter <= norm center := by
    simpa [endpointCenter] using
      norm_selectedBlockRightEndpointCenter_le d n m center
  have hcenterRNorm : norm centerR <= norm center := by
    simpa [centerR] using norm_afterBlocks_le n m (d + 1) center
  change t.sup (schwartzSeminormFamily Real
      (NPointDomain d (m + 1)) Complex)
      (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d m hrho endpointCenter endpointImag centerR yR yR') <= _
  calc
    t.sup (schwartzSeminormFamily Real
        (NPointDomain d (m + 1)) Complex)
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d m hrho endpointCenter endpointImag centerR yR yR') <=
      C * (16 / rho) ^ M *
        (1 + norm endpointCenter) ^ NEndpoint *
        (1 + norm centerR) ^ NTail := hradial
    _ <= C * (16 / rho) ^ M *
        (1 + norm center) ^ NEndpoint *
        (1 + norm center) ^ NTail := by
      gcongr
    _ = C * (16 / rho) ^ M *
        (1 + norm center) ^ (NEndpoint + NTail) := by
      rw [pow_add]
      ring

/-- Dimension-only coefficient that controls a finite seminorm family under
any orthogonal Euclidean rotation. -/
def osiiRotationFinsetSeminormFactor
    (d : Nat) (t : Finset (Nat × Nat)) : Real :=
  ∑ j ∈ t, (d + 1 : Real) ^ (j.1 + j.2)

theorem osiiRotationFinsetSeminormFactor_nonneg
    (d : Nat) (t : Finset (Nat × Nat)) :
    0 <= osiiRotationFinsetSeminormFactor d t := by
  apply Finset.sum_nonneg
  intro j hj
  positivity

/-- A finite seminorm family of a rotated source is controlled uniformly in
the orthogonal matrix. -/
theorem finsetSup_osiiEuclideanRotateSchwartz_le
    (d r : Nat) [NeZero d]
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1)
    (t : Finset (Nat × Nat))
    (f : SchwartzNPoint d r) :
    t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex)
        (osiiEuclideanRotateSchwartz R hR f) <=
      osiiRotationFinsetSeminormFactor d t *
        t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex) f := by
  let Q : Real :=
    t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex) f
  have hQ : 0 <= Q := apply_nonneg _ _
  apply Seminorm.finset_sup_apply_le
    (mul_nonneg (osiiRotationFinsetSeminormFactor_nonneg d t) hQ)
  intro j hj
  have hsource : SchwartzMap.seminorm Real j.1 j.2 f <= Q := by
    simpa only [Q] using
      (Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily Real
          (NPointDomain d r) Complex) hj)
  have hterm :
      (d + 1 : Real) ^ (j.1 + j.2) <=
        osiiRotationFinsetSeminormFactor d t := by
    exact Finset.single_le_sum
      (f := fun z => (d + 1 : Real) ^ (z.1 + z.2))
      (fun z _ => by positivity) hj
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiEuclideanRotateSchwartz R hR f) <=
      (d + 1 : Real) ^ (j.1 + j.2) *
        SchwartzMap.seminorm Real j.1 j.2 f :=
      seminorm_osiiEuclideanRotateSchwartz_le R hR j.1 j.2 f
    _ <= (d + 1 : Real) ^ (j.1 + j.2) * Q :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ <= osiiRotationFinsetSeminormFactor d t * Q :=
      mul_le_mul_of_nonneg_right hterm hQ

/-- The left packet operation, rotation between two time reflections, obeys
the same uniform finite-seminorm estimate. -/
theorem finsetSup_timeReflect_rotate_timeReflect_le
    (d r : Nat) [NeZero d]
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hR : R.transpose * R = 1)
    (t : Finset (Nat × Nat))
    (f : SchwartzNPoint d r) :
    t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex)
        ((osiiEuclideanRotateSchwartz R hR f.timeReflect).timeReflect) <=
      osiiRotationFinsetSeminormFactor d t *
        t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex) f := by
  let Q : Real :=
    t.sup (schwartzSeminormFamily Real (NPointDomain d r) Complex) f
  have hQ : 0 <= Q := apply_nonneg _ _
  apply Seminorm.finset_sup_apply_le
    (mul_nonneg (osiiRotationFinsetSeminormFactor_nonneg d t) hQ)
  intro j hj
  have hsource : SchwartzMap.seminorm Real j.1 j.2 f <= Q := by
    simpa only [Q] using
      (Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily Real
          (NPointDomain d r) Complex) hj)
  have hterm :
      (d + 1 : Real) ^ (j.1 + j.2) <=
        osiiRotationFinsetSeminormFactor d t := by
    exact Finset.single_le_sum
      (f := fun z => (d + 1 : Real) ^ (z.1 + z.2))
      (fun z _ => by positivity) hj
  calc
    SchwartzMap.seminorm Real j.1 j.2
        ((osiiEuclideanRotateSchwartz R hR f.timeReflect).timeReflect) <=
      SchwartzMap.seminorm Real j.1 j.2
        (osiiEuclideanRotateSchwartz R hR f.timeReflect) :=
      SchwartzNPoint.seminorm_timeReflect_le
        (d := d) j.1 j.2
        (osiiEuclideanRotateSchwartz R hR f.timeReflect)
    _ <= (d + 1 : Real) ^ (j.1 + j.2) *
        SchwartzMap.seminorm Real j.1 j.2 f.timeReflect :=
      seminorm_osiiEuclideanRotateSchwartz_le
        R hR j.1 j.2 f.timeReflect
    _ <= (d + 1 : Real) ^ (j.1 + j.2) *
        SchwartzMap.seminorm Real j.1 j.2 f := by
      exact mul_le_mul_of_nonneg_left
        (SchwartzNPoint.seminorm_timeReflect_le
          (d := d) j.1 j.2 f) (by positivity)
    _ <= (d + 1 : Real) ^ (j.1 + j.2) * Q :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ <= osiiRotationFinsetSeminormFactor d t * Q :=
      mul_le_mul_of_nonneg_right hterm hQ

namespace OSIIAxisPairCompactCommonSourcePackage

variable {d n m : Nat} [NeZero d]
variable {leftPositive : SchwartzNPoint d n}
variable {right : SchwartzNPoint d m}

/-- Norm of the rotated positive-time left Hilbert vector controlling one
coordinate chart of a compact common-source packet. -/
noncomputable def flatTubeBranchCoordinateChartLeftNorm
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (a : osiiAxisPairIndex d) : Real :=
  let R := (osiiAxisPairRotationData P.T a).matrix
  let hR := (osiiAxisPairRotationData P.T a).orthogonal
  let leftR : SchwartzNPoint d n :=
    (osiiEuclideanRotateSchwartz R hR P.data.left).timeReflect
  let hleftR :
      tsupport (leftR : NPointDomain d n -> Complex) <=
        OrderedPositiveTimeRegion d n :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR P.data.left)
      (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR P.data.left (P.data.left_support a))
  norm (osiiPositiveTimeSingleVectorCLM OS n ⟨leftR, hleftR⟩)

/-- Right-vector counterpart of
`flatTubeBranchCoordinateChartLeftNorm`. -/
noncomputable def flatTubeBranchCoordinateChartRightNorm
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (a : osiiAxisPairIndex d) : Real :=
  let R := (osiiAxisPairRotationData P.T a).matrix
  let hR := (osiiAxisPairRotationData P.T a).orthogonal
  let rightR : SchwartzNPoint d m :=
    osiiEuclideanRotateSchwartz R hR P.data.right
  let hrightR :
      tsupport (rightR : NPointDomain d m -> Complex) <=
        OrderedPositiveTimeRegion d m :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.data.right (P.data.right_support a)
  norm (osiiPositiveTimeSingleVectorCLM OS m ⟨rightR, hrightR⟩)

/-- The existing coordinate-chart constant is exactly twice the product of
the two named Hilbert-vector norms. -/
theorem flatTubeBranchCoordinateChartBound_eq_norms
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (a : osiiAxisPairIndex d) :
    P.flatTubeBranchCoordinateChartBound OS a =
      2 * P.flatTubeBranchCoordinateChartLeftNorm OS a *
        P.flatTubeBranchCoordinateChartRightNorm OS a := by
  rfl

/-- The chart constant is bounded by the sum of the two diagonal norm
squares. -/
theorem flatTubeBranchCoordinateChartBound_le_normSq_add
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (a : osiiAxisPairIndex d) :
    P.flatTubeBranchCoordinateChartBound OS a <=
      P.flatTubeBranchCoordinateChartLeftNorm OS a ^ 2 +
        P.flatTubeBranchCoordinateChartRightNorm OS a ^ 2 := by
  rw [P.flatTubeBranchCoordinateChartBound_eq_norms]
  nlinarith [sq_nonneg
    (P.flatTubeBranchCoordinateChartLeftNorm OS a -
      P.flatTubeBranchCoordinateChartRightNorm OS a)]

end OSIIAxisPairCompactCommonSourcePackage

set_option maxHeartbeats 1200000 in
/-- The squared norms of both Hilbert vectors underlying every selected-block
coordinate chart have one polynomial inverse-radius and center majorant,
uniformly in the packet slope and active axis.  These are the diagonal
estimates consumed by the reflected-Gram recursion. -/
theorem exists_selectedBlockAxisPairHilbertNormSq_scale_bound
    (d n m : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center : Fin ((n + 1 + m) * (d + 1)) -> Real),
          ∀ hcenter : ∀ i : Fin (n + 1 + m),
            rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))),
              ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) (n + 1 + m) rho,
                ∀ P : OSIIAxisPairCompactCommonSourcePackage
                  (osiiStep4SelectedBlockLeftPositiveTimeSource
                    d n m hrho center p.1 p.2 hcenter).1
                  (osiiStep4SelectedBlockRightPositiveTimeSource
                    d n m hrho center p.1 p.2 hcenter).1,
                  ∀ a : osiiAxisPairIndex d,
                    P.flatTubeBranchCoordinateChartLeftNorm OS a ^ 2 <=
                        C * (16 / rho) ^ M * (1 + norm center) ^ N ∧
                      P.flatTubeBranchCoordinateChartRightNorm OS a ^ 2 <=
                        C * (16 / rho) ^ M * (1 + norm center) ^ N ∧
                      P.flatTubeBranchCoordinateChartLeftNorm OS a ^ 2 +
                          P.flatTubeBranchCoordinateChartRightNorm OS a ^ 2 <=
                        C * (16 / rho) ^ M * (1 + norm center) ^ N := by
  obtain ⟨L, KOS, hKOS, hOS⟩ :=
    exists_osiiPositiveTimeSingleVector_boundedArity_norm_sq_finsetSup_bound
      d (max (n + 1) (m + 1)) OS
  let t : Finset (Nat × Nat) := Finset.Iic (L, L)
  have hOSL := hOS (n + 1) (Nat.le_max_left (n + 1) (m + 1))
  have hOSR := hOS (m + 1) (Nat.le_max_right (n + 1) (m + 1))
  obtain ⟨CL, ML, NL, hCL, hsourceL⟩ :=
    exists_selectedBlockLeftPositiveTimeSource_finsetSeminorm_scale_bound
      d n m t
  obtain ⟨CR, MR, NR, hCR, hsourceR⟩ :=
    exists_selectedBlockRightPositiveTimeSource_finsetSeminorm_scale_bound
      d n m t
  let KRot := osiiRotationFinsetSeminormFactor d t
  let CL2 : Real := KOS * (KRot * CL) ^ 2
  let CR2 : Real := KOS * (KRot * CR) ^ 2
  let ML2 : Nat := ML + ML
  let MR2 : Nat := MR + MR
  let NL2 : Nat := NL + NL
  let NR2 : Nat := NR + NR
  let M : Nat := max ML2 MR2
  let N : Nat := max NL2 NR2
  let C : Real := CL2 + CR2
  have hKRot : 0 <= KRot :=
    osiiRotationFinsetSeminormFactor_nonneg d t
  have hCL2 : 0 <= CL2 :=
    mul_nonneg hKOS (sq_nonneg (KRot * CL))
  have hCR2 : 0 <= CR2 :=
    mul_nonneg hKOS (sq_nonneg (KRot * CR))
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  refine ⟨C, M, N, hC, ?_⟩
  intro rho hrho hrho_le center hcenter p hp P a
  let leftPositive : SchwartzNPoint d (n + 1) :=
    (osiiStep4SelectedBlockLeftPositiveTimeSource
      d n m hrho center p.1 p.2 hcenter).1
  let right : SchwartzNPoint d (m + 1) :=
    (osiiStep4SelectedBlockRightPositiveTimeSource
      d n m hrho center p.1 p.2 hcenter).1
  let R := (osiiAxisPairRotationData P.T a).matrix
  let hR := (osiiAxisPairRotationData P.T a).orthogonal
  let leftR : SchwartzNPoint d (n + 1) :=
    (osiiEuclideanRotateSchwartz R hR P.data.left).timeReflect
  let rightR : SchwartzNPoint d (m + 1) :=
    osiiEuclideanRotateSchwartz R hR P.data.right
  let hleftR :
      tsupport (leftR : NPointDomain d (n + 1) -> Complex) <=
        OrderedPositiveTimeRegion d (n + 1) :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR P.data.left)
      (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR P.data.left (P.data.left_support a))
  let hrightR :
      tsupport (rightR : NPointDomain d (m + 1) -> Complex) <=
        OrderedPositiveTimeRegion d (m + 1) :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.data.right (P.data.right_support a)
  let QL : Real :=
    t.sup (schwartzSeminormFamily Real
      (NPointDomain d (n + 1)) Complex) leftPositive
  let QR : Real :=
    t.sup (schwartzSeminormFamily Real
      (NPointDomain d (m + 1)) Complex) right
  let QRotL : Real :=
    t.sup (schwartzSeminormFamily Real
      (NPointDomain d (n + 1)) Complex) leftR
  let QRotR : Real :=
    t.sup (schwartzSeminormFamily Real
      (NPointDomain d (m + 1)) Complex) rightR
  have hQL : 0 <= QL := apply_nonneg _ _
  have hQR : 0 <= QR := apply_nonneg _ _
  have hQRotL : 0 <= QRotL := apply_nonneg _ _
  have hQRotR : 0 <= QRotR := apply_nonneg _ _
  have hsourceL' :
      QL <= CL * (16 / rho) ^ ML * (1 + norm center) ^ NL := by
    simpa [QL, leftPositive] using
      hsourceL hrho hrho_le center hcenter p hp
  have hsourceR' :
      QR <= CR * (16 / rho) ^ MR * (1 + norm center) ^ NR := by
    simpa [QR, right] using
      hsourceR hrho hrho_le center hcenter p hp
  have hrotL : QRotL <= KRot * QL := by
    have h := finsetSup_timeReflect_rotate_timeReflect_le
      d (n + 1) R hR t leftPositive
    simpa [QRotL, QL, leftR, leftPositive, KRot, P.left_eq] using h
  have hrotR : QRotR <= KRot * QR := by
    have h := finsetSup_osiiEuclideanRotateSchwartz_le
      d (m + 1) R hR t right
    simpa [QRotR, QR, rightR, right, KRot, P.right_eq] using h
  have hnormL := hOSL leftR hleftR
  have hnormR := hOSR rightR hrightR
  let A : Real := 16 / rho
  let Bc : Real := 1 + norm center
  have hA : 1 <= A := by
    dsimp [A]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hBc : 1 <= Bc := by
    dsimp [Bc]
    linarith [norm_nonneg center]
  have hleftSq :
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
        ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ ML2 * Bc ^ NL2 := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <= KOS * QRotL ^ 2 := by
        simpa [QRotL, t] using hnormL
      _ <= KOS * (KRot * QL) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hQRotL hrotL 2) hKOS
      _ <= KOS *
          (KRot * (CL * A ^ ML * Bc ^ NL)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hKOS
        apply pow_le_pow_left₀
        · exact mul_nonneg hKRot hQL
        · exact mul_le_mul_of_nonneg_left
            (by simpa [A, Bc] using hsourceL') hKRot
      _ = CL2 * A ^ ML2 * Bc ^ NL2 := by
        dsimp [CL2, ML2, NL2]
        rw [pow_two, pow_add, pow_add]
        ring
  have hrightSq :
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
        ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ MR2 * Bc ^ NR2 := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <= KOS * QRotR ^ 2 := by
        simpa [QRotR, t] using hnormR
      _ <= KOS * (KRot * QR) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hQRotR hrotR 2) hKOS
      _ <= KOS *
          (KRot * (CR * A ^ MR * Bc ^ NR)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hKOS
        apply pow_le_pow_left₀
        · exact mul_nonneg hKRot hQR
        · exact mul_le_mul_of_nonneg_left
            (by simpa [A, Bc] using hsourceR') hKRot
      _ = CR2 * A ^ MR2 * Bc ^ NR2 := by
        dsimp [CR2, MR2, NR2]
        rw [pow_two, pow_add, pow_add]
        ring
  have hleftSq' :
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
        ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ M * Bc ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ ML2 * Bc ^ NL2 := hleftSq
      _ <= CL2 * A ^ M * Bc ^ NL2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hA (Nat.le_max_left _ _)) hCL2)
          (pow_nonneg (by positivity) _)
      _ <= CL2 * A ^ M * Bc ^ N := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hBc (Nat.le_max_left _ _))
          (mul_nonneg hCL2 (pow_nonneg (by positivity) _))
  have hrightSq' :
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
        ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ M * Bc ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ MR2 * Bc ^ NR2 := hrightSq
      _ <= CR2 * A ^ M * Bc ^ NR2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hA (Nat.le_max_right _ _)) hCR2)
          (pow_nonneg (by positivity) _)
      _ <= CR2 * A ^ M * Bc ^ N := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hBc (Nat.le_max_right _ _))
          (mul_nonneg hCR2 (pow_nonneg (by positivity) _))
  change
    norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
        ⟨leftR, hleftR⟩) ^ 2 <=
        C * (16 / rho) ^ M * (1 + norm center) ^ N ∧
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
        ⟨rightR, hrightR⟩) ^ 2 <=
        C * (16 / rho) ^ M * (1 + norm center) ^ N ∧
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 +
          norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
            ⟨rightR, hrightR⟩) ^ 2 <=
        C * (16 / rho) ^ M * (1 + norm center) ^ N
  have hleftFinal :
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <=
        C * (16 / rho) ^ M * (1 + norm center) ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <=
          CL2 * A ^ M * Bc ^ N := hleftSq'
      _ <= (CL2 + CR2) * A ^ M * Bc ^ N := by
        gcongr
        linarith
      _ = C * (16 / rho) ^ M * (1 + norm center) ^ N := by
        rfl
  have hrightFinal :
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <=
        C * (16 / rho) ^ M * (1 + norm center) ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <=
          CR2 * A ^ M * Bc ^ N := hrightSq'
      _ <= (CL2 + CR2) * A ^ M * Bc ^ N := by
        gcongr
        linarith
      _ = C * (16 / rho) ^ M * (1 + norm center) ^ N := by
        rfl
  refine ⟨hleftFinal, hrightFinal, ?_⟩
  calc
    norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 +
        norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <=
      CL2 * A ^ M * Bc ^ N + CR2 * A ^ M * Bc ^ N :=
        add_le_add hleftSq' hrightSq'
    _ = C * (16 / rho) ^ M * (1 + norm center) ^ N := by
      dsimp [C, A, Bc]
      ring

set_option maxHeartbeats 1200000 in
/-- The explicit coordinate-chart bound of every compact selected-block
axis-pair packet grows at most polynomially in the inverse radial scale and
the real center, uniformly in the packet slope and active axis. -/
theorem exists_selectedBlockAxisPairCoordinateChart_scale_bound
    (d n m : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    ∃ C : Real, ∃ M N : Nat, 0 <= C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho <= 16 ->
        ∀ (center : Fin ((n + 1 + m) * (d + 1)) -> Real),
          ∀ hcenter : ∀ i : Fin (n + 1 + m),
            rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))),
              ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
                  (d + 1) (n + 1 + m) rho,
                ∀ P : OSIIAxisPairCompactCommonSourcePackage
                  (osiiStep4SelectedBlockLeftPositiveTimeSource
                    d n m hrho center p.1 p.2 hcenter).1
                  (osiiStep4SelectedBlockRightPositiveTimeSource
                    d n m hrho center p.1 p.2 hcenter).1,
                  ∀ a : osiiAxisPairIndex d,
                    P.flatTubeBranchCoordinateChartBound OS a <=
                      C * (16 / rho) ^ M * (1 + norm center) ^ N := by
  obtain ⟨C, M, N, hC, hnormSq⟩ :=
    exists_selectedBlockAxisPairHilbertNormSq_scale_bound
      d n m OS
  refine ⟨C, M, N, hC, ?_⟩
  intro rho hrho hrho_le center hcenter p hp P a
  obtain ⟨_hleft, _hright, hsum⟩ :=
    hnormSq hrho hrho_le center hcenter p hp P a
  exact (P.flatTubeBranchCoordinateChartBound_le_normSq_add OS a).trans hsum

end OSReconstruction
