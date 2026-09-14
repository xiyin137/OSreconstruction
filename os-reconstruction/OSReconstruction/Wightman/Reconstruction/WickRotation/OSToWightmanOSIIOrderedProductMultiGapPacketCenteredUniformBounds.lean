/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketCenteredGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds










noncomputable section

open scoped BigOperators Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Centering preserves the original-OS packet bound at any independently
supplied common polynomial degree. -/
theorem
    OSIIChronologicalCompactFactors.norm_compensatedMovingPacket_branchOfOS_centered_cosh_le_of_vector_bounds
    {k : ℕ} [NeZero k]
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (N : ℕ)
    (q : osiiAxisPairMultiGapIndex d k)
    (B : ℝ) (hB : 0 ≤ B)
    (CL CR : ℝ) (hCL : 0 ≤ CL) (hCR : 0 ≤ CR)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (hcenter : ‖F.packetCenterOffsetVector T hordered q‖ ≤ B)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (z : ℂ) (hz : 0 < z.re)
    (hleft :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support T hT hordered x q⟩‖ ^ 2 ≤
        CL * (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^ N)
    (hright :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support T hT hordered x q⟩‖ ^ 2 ≤
        CR * (1 + ‖F.packetRightConfiguration T hordered x q‖) ^ N) :
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (F.packetLeftSource T hordered x q)
        (F.packetLeftSource_support T hT hordered x q)
        (F.packetRightSource T hordered x q)
        (F.packetRightSource_support T hT hordered x q)).branchOfOS
          OS z‖ ≤
      (1 +
          CL *
            (OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
              (d := d) (k := k) B) ^ N +
          CR *
            (OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
              (d := d) (k := k) B) ^ N) *
        Real.exp
          (4 * ((N + N : ℕ) : ℝ) *
            SCV.logCoshGauge
              (osiiAxisPairMultiGapFlatten
                (osiiNarrowTimeCenteredRealLogCoordinate T x))) := by
  let A :=
    OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
      (d := d) (k := k) B
  let G :=
    SCV.logCoshGauge
      (osiiAxisPairMultiGapFlatten
        (osiiNarrowTimeCenteredRealLogCoordinate T x))
  let E := Real.exp (4 * G)
  have hA : 0 < A := by
    dsimp [A,
      OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant]
    have hK :=
      osiiAxisPairCenteredTranslationCoshConstant_nonneg
        (d := d) (k := k)
    linarith
  have hE : 1 ≤ E := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le))
  have hpower (v : ℝ) (hv : 0 ≤ v) (hbound : 1 + v ≤ A * E) :
      (1 + v) ^ N ≤ A ^ N * E ^ (N + N) := by
    calc
      (1 + v) ^ N ≤ (A * E) ^ N :=
        pow_le_pow_left₀ (by linarith) hbound N
      _ = A ^ N * E ^ N := by rw [mul_pow]
      _ ≤ A ^ N * E ^ (N + N) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hE (Nat.le_add_right N N))
          (pow_nonneg hA.le _)
  have hleftPow :
      (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^ N ≤
        A ^ N * E ^ (N + N) := by
    apply hpower _ (norm_nonneg _)
    simpa [A, E, G] using
      F.one_add_norm_packetLeftConfiguration_le_centered_cosh
        T hT hordered x q B hB hcenter
  have hrightPow :
      (1 + ‖F.packetRightConfiguration T hordered x q‖) ^ N ≤
        A ^ N * E ^ (N + N) := by
    apply hpower _ (norm_nonneg _)
    simpa [A, E, G] using
      F.one_add_norm_packetRightConfiguration_le_centered_cosh
        T hT hordered x q B hB hcenter
  have hleftVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support T hT hordered x q⟩‖ ^ 2 ≤
        CL * A ^ N * E ^ (N + N) := by
    calc
      _ ≤ CL * (1 + ‖F.packetLeftConfiguration T hordered x q‖) ^ N :=
        hleft
      _ ≤ CL * (A ^ N * E ^ (N + N)) :=
        mul_le_mul_of_nonneg_left hleftPow hCL
      _ = CL * A ^ N * E ^ (N + N) := by ring
  have hrightVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support T hT hordered x q⟩‖ ^ 2 ≤
        CR * A ^ N * E ^ (N + N) := by
    calc
      _ ≤ CR * (1 + ‖F.packetRightConfiguration T hordered x q‖) ^ N :=
        hright
      _ ≤ CR * (A ^ N * E ^ (N + N)) :=
        mul_le_mul_of_nonneg_left hrightPow hCR
      _ = CR * A ^ N * E ^ (N + N) := by ring
  have hEpow :
      E ^ (N + N) = Real.exp (4 * ((N + N : ℕ) : ℝ) * G) := by
    rw [show E = Real.exp (4 * G) by rfl, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource T hordered x q,
            F.packetLeftPositiveSource_support T hT hordered x q⟩‖ ^ 2 +
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource T hordered x q,
            F.packetRightPositiveSource_support T hT hordered x q⟩‖ ^ 2 :=
      F.norm_compensatedMovingPacket_branchOfOS_le
        OS T hT hordered x q z hz
    _ ≤ (CL * A ^ N + CR * A ^ N) * E ^ (N + N) := by
      nlinarith [hleftVector, hrightVector]
    _ ≤ (1 + CL * A ^ N + CR * A ^ N) * E ^ (N + N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ =
        (1 + CL * A ^ N + CR * A ^ N) *
          Real.exp (4 * ((N + N : ℕ) : ℝ) * G) := by
      rw [hEpow]

end OSReconstruction
