/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformE0PrimeDegree










noncomputable section

open Complex Matrix Metric Set
open scoped Classical

namespace OSReconstruction

/-- Per-particle inverse-scale rate after applying the E0' norm-square
estimate.  The factor two records the square of the source seminorm bound. -/
def OSIIUniformRadialEndpointSourceDegreeData.hilbertScaleRate
    {d : Nat} [NeZero d]
    {t : Finset (Nat × Nat)}
    (D : OSIIUniformRadialEndpointSourceDegreeData d t) : Nat :=
  2 * (3 * (d + 1) + D.scaleOffset)

/-- Per-particle center-growth rate after applying the E0' norm-square
estimate. -/
def OSIIUniformRadialEndpointSourceDegreeData.hilbertGrowthRate
    {d : Nat} [NeZero d]
    {t : Finset (Nat × Nat)}
    (D : OSIIUniformRadialEndpointSourceDegreeData d t) : Nat :=
  2 * (D.endpointDegree + D.tailDegree)

theorem OSIIUniformRadialEndpointSourceDegreeData.leftSourceSqDegree_le
    {d : Nat} [NeZero d]
    {t : Finset (Nat × Nat)}
    (D : OSIIUniformRadialEndpointSourceDegreeData d t)
    (n m : Nat) :
    (3 * (d + 1) * n + D.scaleOffset) +
        (3 * (d + 1) * n + D.scaleOffset) <=
      (n + 1 + m) * D.hilbertScaleRate := by
  simp only [hilbertScaleRate]
  nlinarith

theorem OSIIUniformRadialEndpointSourceDegreeData.rightSourceSqDegree_le
    {d : Nat} [NeZero d]
    {t : Finset (Nat × Nat)}
    (D : OSIIUniformRadialEndpointSourceDegreeData d t)
    (n m : Nat) :
    (3 * (d + 1) * m + D.scaleOffset) +
        (3 * (d + 1) * m + D.scaleOffset) <=
      (n + 1 + m) * D.hilbertScaleRate := by
  simp only [hilbertScaleRate]
  nlinarith

theorem OSIIUniformRadialEndpointSourceDegreeData.sourceSqGrowthDegree_le
    {d : Nat} [NeZero d]
    {t : Finset (Nat × Nat)}
    (D : OSIIUniformRadialEndpointSourceDegreeData d t)
    (n m : Nat) :
    (D.endpointDegree + D.tailDegree) +
        (D.endpointDegree + D.tailDegree) <=
      (n + 1 + m) * D.hilbertGrowthRate := by
  simp only [hilbertGrowthRate]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- Both Hilbert vectors underlying a selected chronological chart obey one
bound whose two degrees are fixed rates times total arity.  Constants may
depend on the split, as allowed by OS II equation `(6.20)`. -/
theorem OSIIUniformRadialEndpointSourceDegreeData.exists_selectedBlockAxisPairHilbertNormSq_bound
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc))
    (n m : Nat) :
    ∃ C : Real, 0 <= C ∧
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
                        C * (16 / rho) ^
                            ((n + 1 + m) * D.hilbertScaleRate) *
                          (1 + norm center) ^
                            ((n + 1 + m) * D.hilbertGrowthRate) ∧
                      P.flatTubeBranchCoordinateChartRightNorm OS a ^ 2 <=
                        C * (16 / rho) ^
                            ((n + 1 + m) * D.hilbertScaleRate) *
                          (1 + norm center) ^
                            ((n + 1 + m) * D.hilbertGrowthRate) ∧
                      P.flatTubeBranchCoordinateChartLeftNorm OS a ^ 2 +
                          P.flatTubeBranchCoordinateChartRightNorm OS a ^ 2 <=
                        C * (16 / rho) ^
                            ((n + 1 + m) * D.hilbertScaleRate) *
                          (1 + norm center) ^
                            ((n + 1 + m) * D.hilbertGrowthRate) := by
  obtain ⟨KOSL, hKOSL, hOSL⟩ :=
    exists_osiiPositiveTimeSingleVector_norm_sq_e0PrimeSeminorms_bound
      d (n + 1) OS lgc
  obtain ⟨KOSR, hKOSR, hOSR⟩ :=
    exists_osiiPositiveTimeSingleVector_norm_sq_e0PrimeSeminorms_bound
      d (m + 1) OS lgc
  obtain ⟨CL, hCL, hsourceL⟩ := D.exists_selectedBlockLeft_bound n m
  obtain ⟨CR, hCR, hsourceR⟩ := D.exists_selectedBlockRight_bound n m
  let t := osiiE0PrimeHilbertSeminorms lgc
  let KRot := osiiRotationFinsetSeminormFactor d t
  let CL2 : Real := KOSL * (KRot * CL) ^ 2
  let CR2 : Real := KOSR * (KRot * CR) ^ 2
  let EL : Nat := 3 * (d + 1) * n + D.scaleOffset
  let ER : Nat := 3 * (d + 1) * m + D.scaleOffset
  let ECenter : Nat := D.endpointDegree + D.tailDegree
  let EL2 : Nat := EL + EL
  let ER2 : Nat := ER + ER
  let ECenter2 : Nat := ECenter + ECenter
  let M : Nat := (n + 1 + m) * D.hilbertScaleRate
  let N : Nat := (n + 1 + m) * D.hilbertGrowthRate
  let C : Real := CL2 + CR2
  have hKRot : 0 <= KRot :=
    osiiRotationFinsetSeminormFactor_nonneg d t
  have hCL2 : 0 <= CL2 :=
    mul_nonneg hKOSL (sq_nonneg (KRot * CL))
  have hCR2 : 0 <= CR2 :=
    mul_nonneg hKOSR (sq_nonneg (KRot * CR))
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hEL2 : EL2 <= M := by
    simpa [EL2, EL, M] using D.leftSourceSqDegree_le n m
  have hER2 : ER2 <= M := by
    simpa [ER2, ER, M] using D.rightSourceSqDegree_le n m
  have hECenter2 : ECenter2 <= N := by
    simpa [ECenter2, ECenter, N] using D.sourceSqGrowthDegree_le n m
  refine ⟨C, hC, ?_⟩
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
      QL <= CL * (16 / rho) ^ EL *
        (1 + norm center) ^ ECenter := by
    simpa [QL, leftPositive, t, EL, ECenter] using
      hsourceL hrho hrho_le center hcenter p hp
  have hsourceR' :
      QR <= CR * (16 / rho) ^ ER *
        (1 + norm center) ^ ECenter := by
    simpa [QR, right, t, ER, ECenter] using
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
  let B : Real := 1 + norm center
  have hA : 1 <= A := by
    dsimp [A]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hB : 1 <= B := by
    dsimp [B]
    linarith [norm_nonneg center]
  have hleftSq :
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
        ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ EL2 * B ^ ECenter2 := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <= KOSL * QRotL ^ 2 := by
        simpa [QRotL, t] using hnormL
      _ <= KOSL * (KRot * QL) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hQRotL hrotL 2) hKOSL
      _ <= KOSL *
          (KRot * (CL * A ^ EL * B ^ ECenter)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hKOSL
        apply pow_le_pow_left₀
        · exact mul_nonneg hKRot hQL
        · exact mul_le_mul_of_nonneg_left
            (by simpa [A, B] using hsourceL') hKRot
      _ = CL2 * A ^ EL2 * B ^ ECenter2 := by
        dsimp [CL2, EL2, ECenter2]
        rw [pow_two, pow_add, pow_add]
        ring
  have hrightSq :
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
        ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ ER2 * B ^ ECenter2 := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <= KOSR * QRotR ^ 2 := by
        simpa [QRotR, t] using hnormR
      _ <= KOSR * (KRot * QR) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hQRotR hrotR 2) hKOSR
      _ <= KOSR *
          (KRot * (CR * A ^ ER * B ^ ECenter)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hKOSR
        apply pow_le_pow_left₀
        · exact mul_nonneg hKRot hQR
        · exact mul_le_mul_of_nonneg_left
            (by simpa [A, B] using hsourceR') hKRot
      _ = CR2 * A ^ ER2 * B ^ ECenter2 := by
        dsimp [CR2, ER2, ECenter2]
        rw [pow_two, pow_add, pow_add]
        ring
  have hleftSq' :
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
        ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ M * B ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (n + 1)
          ⟨leftR, hleftR⟩) ^ 2 <=
          CL2 * A ^ EL2 * B ^ ECenter2 := hleftSq
      _ <= CL2 * A ^ M * B ^ ECenter2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hA hEL2) hCL2)
          (pow_nonneg (by positivity) _)
      _ <= CL2 * A ^ M * B ^ N := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB hECenter2)
          (mul_nonneg hCL2 (pow_nonneg (by positivity) _))
  have hrightSq' :
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
        ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ M * B ^ N := by
    calc
      norm (osiiPositiveTimeSingleVectorCLM OS (m + 1)
          ⟨rightR, hrightR⟩) ^ 2 <=
          CR2 * A ^ ER2 * B ^ ECenter2 := hrightSq
      _ <= CR2 * A ^ M * B ^ ECenter2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hA hER2) hCR2)
          (pow_nonneg (by positivity) _)
      _ <= CR2 * A ^ M * B ^ N := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB hECenter2)
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
          ⟨leftR, hleftR⟩) ^ 2 <= CL2 * A ^ M * B ^ N := hleftSq'
      _ <= (CL2 + CR2) * A ^ M * B ^ N := by
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
          ⟨rightR, hrightR⟩) ^ 2 <= CR2 * A ^ M * B ^ N := hrightSq'
      _ <= (CL2 + CR2) * A ^ M * B ^ N := by
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
      CL2 * A ^ M * B ^ N + CR2 * A ^ M * B ^ N :=
        add_le_add hleftSq' hrightSq'
    _ = C * (16 / rho) ^ M * (1 + norm center) ^ N := by
      dsimp [C, A, B]
      ring

set_option maxHeartbeats 1600000 in
/-- The coordinate-chart constant inherits the same rates-times-arity
bound from the two Hilbert norm squares. -/
theorem OSIIUniformRadialEndpointSourceDegreeData.exists_selectedBlockAxisPairCoordinateChart_bound
    {d : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (lgc : OSFixedOrderGrowthCondition d OS)
    (D : OSIIUniformRadialEndpointSourceDegreeData d
      (osiiE0PrimeHilbertSeminorms lgc))
    (n m : Nat) :
    ∃ C : Real, 0 <= C ∧
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
                      C * (16 / rho) ^
                          ((n + 1 + m) * D.hilbertScaleRate) *
                        (1 + norm center) ^
                          ((n + 1 + m) * D.hilbertGrowthRate) := by
  obtain ⟨C, hC, hnormSq⟩ :=
    D.exists_selectedBlockAxisPairHilbertNormSq_bound lgc n m
  refine ⟨C, hC, ?_⟩
  intro rho hrho hrho_le center hcenter p hp P a
  obtain ⟨_hleft, _hright, hsum⟩ :=
    hnormSq hrho hrho_le center hcenter p hp P a
  exact (P.flatTubeBranchCoordinateChartBound_le_normSq_add OS a).trans hsum

end OSReconstruction
