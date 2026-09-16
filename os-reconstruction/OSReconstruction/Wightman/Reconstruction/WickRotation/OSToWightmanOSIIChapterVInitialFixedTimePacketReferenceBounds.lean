import Mathlib.Topology.Algebra.Module.Multilinear.Bounded
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialFixedTimePacket
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketCenteredUniformBounds

/-!
# Uniform packet-reference bounds for the initial fixed-time exhaustion

The coherent one-point carrier multipliers are uniformly bounded on every
fixed Schwartz source.  Since the packet reference sources are finite product
tensors of those localized factors, their full level families are bounded in
the corresponding multi-point Schwartz spaces.

This is the source-side input needed to make the left/right OS Hilbert-vector
coefficients uniform in the spatial exhaustion level.
-/

noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

namespace InitialBaseTimePartitionData

variable {φ : SchwartzMap (Fin k → ℝ) ℂ}

/-- For a fixed one-point source, localization by one coherent carrier factor
is a bounded family in one-point Schwartz topology. -/
theorem fixedTimePacketData_localizedFactor_isVonNBounded
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun N : ℕ =>
        SchwartzMap.smulLeftCLM ℂ
          (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a).factors i)
          f) := by
  rw [
    (schwartz_withSeminorms ℝ
      (SpacetimeDim d) ℂ).isVonNBounded_iff_seminorm_bounded]
  intro pq
  obtain ⟨M, hM, hbound⟩ :=
    D.quantitativeFixedTimePacketData_factor_smul_uniform_seminorm_bound
      hφ_compact a i f pq.1 pq.2
  refine ⟨M + 1, by linarith, ?_⟩
  intro g hg
  rcases hg with ⟨N, rfl⟩
  have hle :
      (SchwartzMap.seminorm ℝ pq.1 pq.2)
        (SchwartzMap.smulLeftCLM ℂ
          (((D.quantitativeFixedTimePacketData hφ_compact N
            ).quantitativeLevelCover.carrier a).factors i)
          f) ≤ M := hbound N
  exact lt_of_le_of_lt
    (by
      change
        (SchwartzMap.seminorm ℝ pq.1 pq.2)
          (SchwartzMap.smulLeftCLM ℂ
            (((D.quantitativeFixedTimePacketData hφ_compact N
              ).quantitativeLevelCover.carrier a).factors i)
            f) ≤ M
      exact hle)
    (lt_add_of_pos_right M zero_lt_one)

/-- Conjugating the localized one-point factors preserves level-uniform
Schwartz boundedness. -/
theorem fixedTimePacketData_localizedFactor_conj_isVonNBounded
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun N : ℕ =>
        (SchwartzMap.smulLeftCLM ℂ
          (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a).factors i)
          f).conj) := by
  rw [
    (schwartz_withSeminorms ℝ
      (SpacetimeDim d) ℂ).isVonNBounded_iff_seminorm_bounded]
  intro pq
  obtain ⟨M, hM, hbound⟩ :=
    D.quantitativeFixedTimePacketData_factor_smul_uniform_seminorm_bound
      hφ_compact a i f pq.1 pq.2
  refine ⟨M + 1, by linarith, ?_⟩
  intro g hg
  rcases hg with ⟨N, rfl⟩
  have hle :
      (SchwartzMap.seminorm ℝ pq.1 pq.2)
        (SchwartzMap.smulLeftCLM ℂ
          (((D.quantitativeFixedTimePacketData hφ_compact N
            ).quantitativeLevelCover.carrier a).factors i)
          f) ≤ M := hbound N
  exact lt_of_le_of_lt
    ((SchwartzMap.seminorm_conj_le pq.1 pq.2 _).trans
      (by
        change
          (SchwartzMap.seminorm ℝ pq.1 pq.2)
            (SchwartzMap.smulLeftCLM ℂ
              (((D.quantitativeFixedTimePacketData hφ_compact N
                ).quantitativeLevelCover.carrier a).factors i)
              f) ≤ M
        exact hle))
    (lt_add_of_pos_right M zero_lt_one)

/-- For a fixed source tuple and split, the right packet reference tensors are
bounded uniformly in the spatial exhaustion level. -/
theorem fixedTimePacketData_packetRightReference_isVonNBounded
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun N : ℕ =>
        ((((D.fixedTimePacketData hφ_compact N).levelCover.carrier a
          ).sourcewiseLocalizedFactors fs).packetRightReference q)) := by
  let factors :
      ℕ → Fin (osiiChronologicalGapRightArity q.1) → SchwartzSpacetime d :=
    fun N j =>
      SchwartzMap.smulLeftCLM ℂ
        (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a).factors
          (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))
        (fs (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))
  have hfactors :
      Bornology.IsVonNBounded ℝ (Set.range factors) := by
    rw [Bornology.isVonNBounded_pi_iff]
    intro j
    have hj :=
      D.fixedTimePacketData_localizedFactor_isVonNBounded
        hφ_compact a
        (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j))
        (fs (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))
    rw [← Set.range_comp']
    simpa [factors, Function.comp_def] using hj
  have hproduct :=
    hfactors.image_multilinear
      ((SchwartzMap.productTensorMLM
        (E := SpacetimeDim d)
        (osiiChronologicalGapRightArity q.1)).restrictScalars ℝ)
  rw [← Set.range_comp'] at hproduct
  simpa [factors, Function.comp_def,
    OSIIChronologicalCompactFactors.packetRightReference,
    OSIIChronologicalCompactFactors.sourcewiseLocalizedFactors] using hproduct

/-- For a fixed source tuple and split, the reflected left packet reference
tensors are bounded uniformly in the spatial exhaustion level. -/
theorem fixedTimePacketData_packetLeftReference_isVonNBounded
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun N : ℕ =>
        ((((D.fixedTimePacketData hφ_compact N).levelCover.carrier a
          ).sourcewiseLocalizedFactors fs).packetLeftReference q)) := by
  let factors :
      ℕ → Fin (osiiChronologicalGapLeftArity q.1) → SchwartzSpacetime d :=
    fun N j =>
      let rj : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev j
      let oi : Fin (k + 1) :=
        osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
      (SchwartzMap.smulLeftCLM ℂ
        (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a).factors oi)
        (fs oi)).conj
  have hfactors :
      Bornology.IsVonNBounded ℝ (Set.range factors) := by
    rw [Bornology.isVonNBounded_pi_iff]
    intro j
    let rj : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev j
    let oi : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
    have hj :=
      D.fixedTimePacketData_localizedFactor_conj_isVonNBounded
        hφ_compact a oi (fs oi)
    rw [← Set.range_comp']
    simpa [factors, rj, oi, Function.comp_def] using hj
  have hproduct :=
    hfactors.image_multilinear
      ((SchwartzMap.productTensorMLM
        (E := SpacetimeDim d)
        (osiiChronologicalGapLeftArity q.1)).restrictScalars ℝ)
  rw [← Set.range_comp'] at hproduct
  simpa [factors, Function.comp_def,
    OSIIChronologicalCompactFactors.packetLeftReference,
    OSIIChronologicalCompactFactors.sourcewiseLocalizedFactors] using hproduct

/-- The physical left packet vectors attached to one fixed-time piece have a
single growth coefficient valid at every spatial exhaustion level. -/
theorem fixedTimePacketData_exists_packetLeftVector_norm_sq_bound_uniform_level
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (x : Fin k → osiiAxisPairIndex d → ℝ),
        let P := D.fixedTimePacketData hφ_compact N
        let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
        let hordered :=
          (P.levelCover.carrier a
            ).sourcewiseLocalizedFactors_axisPairOrdered
              P.slope (P.ordered a) fs
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource P.slope hordered x q,
            F.packetLeftPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
          C *
            (1 + ‖F.packetLeftConfiguration
              P.slope hordered x q‖) ^
                ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) := by
  let reference :
      ℕ → SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
    fun N =>
      (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a
        ).sourcewiseLocalizedFactors fs).packetLeftReference q
  obtain ⟨C, hC, hbound⟩ :=
    exists_osiiPacketLeftPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
      OS q reference
        (by
          simpa [reference] using
            D.fixedTimePacketData_packetLeftReference_isVonNBounded
              hφ_compact a fs q)
  refine ⟨C, hC, ?_⟩
  intro N x
  let P := D.fixedTimePacketData hφ_compact N
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let c := F.packetLeftConfiguration P.slope hordered x q
  have heq :
      F.packetLeftPositiveSource P.slope hordered x q =
        osiiPacketLeftPositiveCLM P.slope q
          (translateSchwartzConfiguration c (reference N)) := by
    simpa [P, F, reference, c] using
      F.packetLeftPositiveSource_eq_configurationTranslate
        P.slope hordered x q
  have hs :
      tsupport
          (osiiPacketLeftPositiveCLM P.slope q
              (translateSchwartzConfiguration c (reference N)) :
            NPointDomain d
              (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapLeftArity q.1) := by
    rw [← heq]
    exact F.packetLeftPositiveSource_support
      P.slope P.slope_gt_one hordered x q
  let u :
      euclideanPositiveTimeSubmodule
        (d := d) (osiiChronologicalGapLeftArity q.1) :=
    ⟨F.packetLeftPositiveSource P.slope hordered x q,
      F.packetLeftPositiveSource_support
        P.slope P.slope_gt_one hordered x q⟩
  let v :
      euclideanPositiveTimeSubmodule
        (d := d) (osiiChronologicalGapLeftArity q.1) :=
    ⟨osiiPacketLeftPositiveCLM P.slope q
        (translateSchwartzConfiguration c (reference N)), hs⟩
  have huv : u = v := by
    apply Subtype.ext
    exact heq
  change
    ‖osiiPositiveTimeSingleVectorCLM OS
        (osiiChronologicalGapLeftArity q.1) u‖ ^ 2 ≤
      C * (1 + ‖F.packetLeftConfiguration
        P.slope hordered x q‖) ^
          ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1)))
  calc
    _ =
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1) v‖ ^ 2 := by
      rw [huv]
    _ ≤ C * (1 + ‖c‖) ^
          ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) :=
      hbound N P.slope c hs
    _ =
        C * (1 + ‖F.packetLeftConfiguration
          P.slope hordered x q‖) ^
            ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) := by
      rfl

/-- The physical right packet vectors attached to one fixed-time piece have
the corresponding level-independent growth coefficient. -/
theorem fixedTimePacketData_exists_packetRightVector_norm_sq_bound_uniform_level
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (x : Fin k → osiiAxisPairIndex d → ℝ),
        let P := D.fixedTimePacketData hφ_compact N
        let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
        let hordered :=
          (P.levelCover.carrier a
            ).sourcewiseLocalizedFactors_axisPairOrdered
              P.slope (P.ordered a) fs
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource P.slope hordered x q,
            F.packetRightPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
          C *
            (1 + ‖F.packetRightConfiguration
              P.slope hordered x q‖) ^
                ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) := by
  let reference :
      ℕ → SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
    fun N =>
      (((D.fixedTimePacketData hφ_compact N).levelCover.carrier a
        ).sourcewiseLocalizedFactors fs).packetRightReference q
  obtain ⟨C, hC, hbound⟩ :=
    exists_osiiPacketRightPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
      OS q reference
        (by
          simpa [reference] using
            D.fixedTimePacketData_packetRightReference_isVonNBounded
              hφ_compact a fs q)
  refine ⟨C, hC, ?_⟩
  intro N x
  let P := D.fixedTimePacketData hφ_compact N
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let c := F.packetRightConfiguration P.slope hordered x q
  have heq :
      F.packetRightPositiveSource P.slope hordered x q =
        osiiPacketRightPositiveCLM P.slope q
          (translateSchwartzConfiguration c (reference N)) := by
    simpa [P, F, reference, c] using
      F.packetRightPositiveSource_eq_configurationTranslate
        P.slope hordered x q
  have hs :
      tsupport
          (osiiPacketRightPositiveCLM P.slope q
              (translateSchwartzConfiguration c (reference N)) :
            NPointDomain d
              (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapRightArity q.1) := by
    rw [← heq]
    exact F.packetRightPositiveSource_support
      P.slope P.slope_gt_one hordered x q
  let u :
      euclideanPositiveTimeSubmodule
        (d := d) (osiiChronologicalGapRightArity q.1) :=
    ⟨F.packetRightPositiveSource P.slope hordered x q,
      F.packetRightPositiveSource_support
        P.slope P.slope_gt_one hordered x q⟩
  let v :
      euclideanPositiveTimeSubmodule
        (d := d) (osiiChronologicalGapRightArity q.1) :=
    ⟨osiiPacketRightPositiveCLM P.slope q
        (translateSchwartzConfiguration c (reference N)), hs⟩
  have huv : u = v := by
    apply Subtype.ext
    exact heq
  change
    ‖osiiPositiveTimeSingleVectorCLM OS
        (osiiChronologicalGapRightArity q.1) u‖ ^ 2 ≤
      C * (1 + ‖F.packetRightConfiguration
        P.slope hordered x q‖) ^
          ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1)))
  calc
    _ =
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1) v‖ ^ 2 := by
      rw [huv]
    _ ≤ C * (1 + ‖c‖) ^
          ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) :=
      hbound N P.slope c hs
    _ =
        C * (1 + ‖F.packetRightConfiguration
          P.slope hordered x q‖) ^
            ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) := by
      rfl

/-- For one fixed-time partition piece and one source tuple, the compensated
packet branch has one centered-cosh coefficient valid at every spatial level.
-/
theorem fixedTimePacketData_exists_compensatedMovingPacket_centered_cosh_bound_uniform_level
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (level : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ)
        (z : ℂ), 0 < z.re →
        let P := D.fixedTimePacketData hφ_compact level
        let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
        let hordered :=
          (P.levelCover.carrier a
            ).sourcewiseLocalizedFactors_axisPairOrdered
              P.slope (P.ordered a) fs
        ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
            P.slope P.slope_gt_one
            (osiiAxisPairPositiveCoefficients (x q.1))
            (fun b =>
              le_of_lt
                (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
            q.2
            (F.packetLeftSource P.slope hordered x q)
            (F.packetLeftSource_support
              P.slope P.slope_gt_one hordered x q)
            (F.packetRightSource P.slope hordered x q)
            (F.packetRightSource_support
              P.slope P.slope_gt_one hordered x q)).branch
              OS lgc z‖ ≤
          C *
            Real.exp
              (osiiOriginalOSUniformPacketCoshRate OS k *
                SCV.logCoshGauge
                  (osiiAxisPairMultiGapFlatten
                    (osiiNarrowTimeCenteredRealLogCoordinate
                      P.slope x))) := by
  let m := (osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))
  obtain ⟨CL, hCL, hleft⟩ :=
    D.fixedTimePacketData_exists_packetLeftVector_norm_sq_bound_uniform_level
      hφ_compact a fs OS lgc q
  obtain ⟨CR, hCR, hright⟩ :=
    D.fixedTimePacketData_exists_packetRightVector_norm_sq_bound_uniform_level
      hφ_compact a fs OS lgc q
  let B := 2 * (D.commonLevelCarrierTimeRadius hφ_compact + 1) + 1
  have htime :
      0 ≤ D.commonLevelCarrierTimeRadius hφ_compact := by
    exact le_trans (D.levelCarrierTimeRadius_pos a hφ_compact).le
      (D.levelCarrierTimeRadius_le_common a hφ_compact)
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith
  let A :=
    OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant
      (d := d) (k := k) B
  let rate := osiiOriginalOSUniformPacketCoshRate OS k
  let C : ℝ := 1 + CL * A ^ m + CR * A ^ m
  have hA : 0 < A := by
    dsimp [A,
      OSIIChronologicalCompactFactors.packetConfigurationCenteredCoshConstant]
    have hK :=
      osiiAxisPairCenteredTranslationCoshConstant_nonneg
        (d := d) (k := k)
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have hAm : 0 ≤ A ^ m := pow_nonneg hA.le _
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro level x z hz
  let P := D.fixedTimePacketData hφ_compact level
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let G :=
    SCV.logCoshGauge
      (osiiAxisPairMultiGapFlatten
        (osiiNarrowTimeCenteredRealLogCoordinate P.slope x))
  let E := Real.exp (4 * G)
  have hE : 1 ≤ E := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ =>
          (Real.cosh_pos _).le))
  have hcenter :
      ‖F.packetCenterOffsetVector P.slope hordered q‖ ≤ B := by
    convert
      (D.quantitativeFixedTimePacketData hφ_compact level
        ).sourcewiseLocalized_norm_packetCenterOffsetVector_le a fs q using 1
    apply congrArg norm
    congr 1
  have hleftConfig :
      1 + ‖F.packetLeftConfiguration P.slope hordered x q‖ ≤
        A * E := by
    simpa [A, E, G] using
      F.one_add_norm_packetLeftConfiguration_le_centered_cosh
        P.slope P.slope_gt_one hordered x q B hB hcenter
  have hrightConfig :
      1 + ‖F.packetRightConfiguration P.slope hordered x q‖ ≤
        A * E := by
    simpa [A, E, G] using
      F.one_add_norm_packetRightConfiguration_le_centered_cosh
        P.slope P.slope_gt_one hordered x q B hB hcenter
  have hleftPow :
      (1 + ‖F.packetLeftConfiguration P.slope hordered x q‖) ^ m ≤
        A ^ m * E ^ (m + m) := by
    calc
      (1 + ‖F.packetLeftConfiguration P.slope hordered x q‖) ^ m
          ≤ (A * E) ^ m :=
        pow_le_pow_left₀ (by positivity) hleftConfig m
      _ = A ^ m * E ^ m := by rw [mul_pow]
      _ ≤ A ^ m * E ^ (m + m) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA.le _)
        exact pow_le_pow_right₀ hE (Nat.le_add_right m m)
  have hrightPow :
      (1 + ‖F.packetRightConfiguration P.slope hordered x q‖) ^ m ≤
        A ^ m * E ^ (m + m) := by
    calc
      (1 + ‖F.packetRightConfiguration P.slope hordered x q‖) ^ m
          ≤ (A * E) ^ m :=
        pow_le_pow_left₀ (by positivity) hrightConfig m
      _ = A ^ m * E ^ m := by rw [mul_pow]
      _ ≤ A ^ m * E ^ (m + m) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA.le _)
        exact pow_le_pow_right₀ hE (Nat.le_add_right m m)
  have hleftVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource P.slope hordered x q,
            F.packetLeftPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
        CL * A ^ m * E ^ (m + m) := by
    calc
      _ ≤ CL *
          (1 + ‖F.packetLeftConfiguration
            P.slope hordered x q‖) ^ m := by
        simpa [P, F, hordered, m] using hleft level x
      _ ≤ CL * (A ^ m * E ^ (m + m)) :=
        mul_le_mul_of_nonneg_left hleftPow hCL
      _ = CL * A ^ m * E ^ (m + m) := by ring
  have hrightVector :
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource P.slope hordered x q,
            F.packetRightPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
        CR * A ^ m * E ^ (m + m) := by
    calc
      _ ≤ CR *
          (1 + ‖F.packetRightConfiguration
            P.slope hordered x q‖) ^ m := by
        simpa [P, F, hordered, m] using hright level x
      _ ≤ CR * (A ^ m * E ^ (m + m)) :=
        mul_le_mul_of_nonneg_left hrightPow hCR
      _ = CR * A ^ m * E ^ (m + m) := by ring
  have hbranch :=
    F.norm_compensatedMovingPacket_branch_le
      OS lgc P.slope P.slope_gt_one hordered x q z hz
  have hEpow :
      E ^ (m + m) = Real.exp (rate * G) := by
    rw [show E = Real.exp (4 * G) by rfl]
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [rate, m, osiiOriginalOSUniformPacketCoshRate]
    push_cast
    ring
  calc
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        P.slope P.slope_gt_one
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (F.packetLeftSource P.slope hordered x q)
        (F.packetLeftSource_support
          P.slope P.slope_gt_one hordered x q)
        (F.packetRightSource P.slope hordered x q)
        (F.packetRightSource_support
          P.slope P.slope_gt_one hordered x q)).branch
          OS lgc z‖
        ≤
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1)
          ⟨F.packetLeftPositiveSource P.slope hordered x q,
            F.packetLeftPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 +
        ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          ⟨F.packetRightPositiveSource P.slope hordered x q,
            F.packetRightPositiveSource_support
              P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 :=
      hbranch
    _ ≤ (CL * A ^ m + CR * A ^ m) * E ^ (m + m) := by
      calc
        _ ≤
            CL * A ^ m * E ^ (m + m) +
              CR * A ^ m * E ^ (m + m) :=
          add_le_add hleftVector hrightVector
        _ = (CL * A ^ m + CR * A ^ m) * E ^ (m + m) := by
          ring
    _ ≤ C * E ^ (m + m) := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]
        linarith
      · positivity
    _ = C * Real.exp (rate * G) := by rw [hEpow]
    _ =
        C *
          Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiNarrowTimeCenteredRealLogCoordinate
                    P.slope x))) := by
      rfl

/-- The physical centered estimate transported to one logarithmic packet
chart. The coefficient is uniform in the spatial exhaustion level. -/
theorem fixedTimePacketData_exists_multiGapPacketFamily_chart_centered_cosh_bound_uniform_level
    (D : InitialBaseTimePartitionData (d := d) φ)
    (hφ_compact : HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (a : D.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (level : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ) (w : ℂ),
          |w.im| < Real.pi / 2 →
          let P := D.fixedTimePacketData hφ_compact level
          let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
          let hordered :=
            (P.levelCover.carrier a
              ).sourcewiseLocalizedFactors_axisPairOrdered
                P.slope (P.ordered a) fs
          ‖(F.multiGapPacketFamily
              OS lgc P.slope P.slope_gt_one hordered).logBranch x q
              (osiiAxisPairMultiGapUpdate
                (osiiAxisPairSimultaneousLogRealEmbed x) q w)‖ ≤
            C *
              Real.exp
                (osiiOriginalOSUniformPacketCoshRate OS k *
                  SCV.logCoshGauge
                    (osiiAxisPairMultiGapFlatten
                      (osiiNarrowTimeCenteredRealLogCoordinate
                        P.slope
                        (osiiAxisPairMultiGapChartRealPart x q w)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    D.fixedTimePacketData_exists_compensatedMovingPacket_centered_cosh_bound_uniform_level
      hφ_compact a fs OS lgc q
  refine ⟨C, hC, ?_⟩
  intro level x w hw
  dsimp only
  let P := D.fixedTimePacketData hφ_compact level
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let y := osiiAxisPairMultiGapChartRealPart x q w
  let packet :=
    F.multiGapPacketFamily
      OS lgc P.slope P.slope_gt_one hordered
  have hxy :
      ∀ p : osiiAxisPairMultiGapIndex d k, p ≠ q →
        x p.1 p.2 = y p.1 p.2 := by
    intro p hp
    exact
      (osiiAxisPairMultiGapChartRealPart_eq_of_ne
        x q p w hp).symm
  have hbranch :
      packet.logBranch x q = packet.logBranch y q :=
    packet.logBranch_congr_of_eq_off_selected q hxy
  have hexpRe : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  have hphysical := hbound level y (Complex.exp w) hexpRe
  let z :=
    osiiAxisPairMultiGapUpdate
      (osiiAxisPairSimultaneousLogRealEmbed x) q w
  calc
    ‖packet.logBranch x q z‖ =
        ‖packet.logBranch y q z‖ := by
      rw [congrFun hbranch z]
    _ ≤
        C *
          Real.exp
            (osiiOriginalOSUniformPacketCoshRate OS k *
              SCV.logCoshGauge
                (osiiAxisPairMultiGapFlatten
                  (osiiNarrowTimeCenteredRealLogCoordinate P.slope y))) := by
      simpa [P, F, hordered, packet, y, z,
        OSIIChronologicalCompactFactors.multiGapPacketFamily,
        OSIIAxisPairMultiGapSemigroupPacketFamily.logBranch,
        OSIIAxisPairMultiGapSemigroupPacketFamily.ofCompensatedFrozenDependent,
        OSIIAxisPairGapRotatedSourcePacket.branch,
        osiiAxisPairMultiGapUpdate] using hphysical

end InitialBaseTimePartitionData

end OSIIChapterV
end OSReconstruction
