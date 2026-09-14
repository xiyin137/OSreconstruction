/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketCarrierCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketUniformBounds















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The minimal scale-uniform physical-vector input for the centered packet
argument, formulated using the canonical scale-coherent packet selection. -/
def HasUniformPhysicalPacketVectorBounds
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : Prop :=
  ∀ (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k),
      ∃ CL CR : ℝ, 0 ≤ CL ∧ 0 ≤ CR ∧
        ∀ (timeScale spatialLevel : ℕ)
          (x : Fin k → osiiAxisPairIndex d → ℝ),
            let P := A.commonPacketAt timeScale spatialLevel
            let F :=
              (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
            let hordered :=
              (P.levelCover.carrier a
                ).sourcewiseLocalizedFactors_axisPairOrdered
                  P.slope (P.ordered a) fs
            ‖osiiPositiveTimeSingleVectorCLM OS
                (osiiChronologicalGapLeftArity q.1)
                ⟨F.packetLeftPositiveSource P.slope hordered x q,
                  F.packetLeftPositiveSource_support
                    P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
              CL *
                (1 + ‖F.packetLeftConfiguration
                  P.slope hordered x q‖) ^
                    ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1))) ∧
            ‖osiiPositiveTimeSingleVectorCLM OS
                (osiiChronologicalGapRightArity q.1)
                ⟨F.packetRightPositiveSource P.slope hordered x q,
                  F.packetRightPositiveSource_support
                    P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
              CR *
                (1 + ‖F.packetRightConfiguration
                  P.slope hordered x q‖) ^
                    ((osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) + (osiiOriginalOSBoundedStateSourceOrder OS (k + 1)))

/-- Conjugating the localized coherent one-point factors preserves
level-uniform Schwartz boundedness. -/
theorem commonCoherentLevelFactor_smul_conj_isVonNBounded
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (i : Fin (k + 1))
    (f : SchwartzSpacetime d) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun level : ℕ =>
        (SchwartzMap.smulLeftCLM ℂ
          (A.commonCoherentLevelFactor a level i) f).conj) := by
  rw [
    (schwartz_withSeminorms ℝ
      (SpacetimeDim d) ℂ).isVonNBounded_iff_seminorm_bounded]
  intro pq
  obtain ⟨M, hM, hbound⟩ :=
    A.commonCoherentLevelFactor_smul_uniform_seminorm_bound
      a i f pq.1 pq.2
  refine ⟨M + 1, by linarith, ?_⟩
  intro g hg
  rcases hg with ⟨level, rfl⟩
  exact
    ((SchwartzMap.seminorm_conj_le pq.1 pq.2 _).trans
      (hbound level)).trans_lt
        (lt_add_of_pos_right M zero_lt_one)

/-- The reflected left packet reference tensors of the coherent packet are
bounded uniformly in the spatial level. -/
theorem commonPacketAt_packetLeftReference_isVonNBounded
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun level : ℕ =>
        (((A.commonCoherentLevelFactors a level
          ).sourcewiseLocalizedFactors fs).packetLeftReference q)) := by
  let factors :
      ℕ → Fin (osiiChronologicalGapLeftArity q.1) →
        SchwartzSpacetime d :=
    fun level j =>
      let rj : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev j
      let oi : Fin (k + 1) :=
        osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
      (SchwartzMap.smulLeftCLM ℂ
        (A.commonCoherentLevelFactor a level oi) (fs oi)).conj
  have hfactors :
      Bornology.IsVonNBounded ℝ (Set.range factors) := by
    rw [Bornology.isVonNBounded_pi_iff]
    intro j
    let rj : Fin (osiiChronologicalGapLeftArity q.1) := Fin.rev j
    let oi : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
    have hj :=
      A.commonCoherentLevelFactor_smul_conj_isVonNBounded
        a oi (fs oi)
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
    OSIIChronologicalCompactFactors.sourcewiseLocalizedFactors,
    commonCoherentLevelFactors] using hproduct

/-- The right packet reference tensors of the coherent packet are bounded
uniformly in the spatial level. -/
theorem commonPacketAt_packetRightReference_isVonNBounded
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun level : ℕ =>
        (((A.commonCoherentLevelFactors a level
          ).sourcewiseLocalizedFactors fs).packetRightReference q)) := by
  let factors :
      ℕ → Fin (osiiChronologicalGapRightArity q.1) →
        SchwartzSpacetime d :=
    fun level j =>
      let oi : Fin (k + 1) :=
        osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)
      SchwartzMap.smulLeftCLM ℂ
        (A.commonCoherentLevelFactor a level oi) (fs oi)
  have hfactors :
      Bornology.IsVonNBounded ℝ (Set.range factors) := by
    rw [Bornology.isVonNBounded_pi_iff]
    intro j
    let oi : Fin (k + 1) :=
      osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)
    have hj :=
      A.commonCoherentLevelFactor_smul_isVonNBounded
        a oi (fs oi)
    rw [← Set.range_comp']
    simpa [factors, oi, Function.comp_def] using hj
  have hproduct :=
    hfactors.image_multilinear
      ((SchwartzMap.productTensorMLM
        (E := SpacetimeDim d)
        (osiiChronologicalGapRightArity q.1)).restrictScalars ℝ)
  rw [← Set.range_comp'] at hproduct
  simpa [factors, Function.comp_def,
    OSIIChronologicalCompactFactors.packetRightReference,
    OSIIChronologicalCompactFactors.sourcewiseLocalizedFactors,
    commonCoherentLevelFactors] using hproduct

/-- Ordinary E0 bounds both physical packet vectors uniformly in the
shrinking-time scale and spatial exhaustion level. -/
theorem exists_uniformPhysicalPacketVectorBounds_ofOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (a : A.partition.index)
    (fs : Fin (k + 1) → SchwartzSpacetime d)
    (q : osiiAxisPairMultiGapIndex d k) :
    ∃ CL CR : ℝ, 0 ≤ CL ∧ 0 ≤ CR ∧
      ∀ (timeScale spatialLevel : ℕ)
        (x : Fin k → osiiAxisPairIndex d → ℝ),
          let P := A.commonPacketAt timeScale spatialLevel
          let F :=
            (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
          let hordered :=
            (P.levelCover.carrier a
              ).sourcewiseLocalizedFactors_axisPairOrdered
                P.slope (P.ordered a) fs
          ‖osiiPositiveTimeSingleVectorCLM OS
              (osiiChronologicalGapLeftArity q.1)
              ⟨F.packetLeftPositiveSource P.slope hordered x q,
                F.packetLeftPositiveSource_support
                  P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
            CL *
              (1 + ‖F.packetLeftConfiguration
                P.slope hordered x q‖) ^
                  (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                    osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) ∧
          ‖osiiPositiveTimeSingleVectorCLM OS
              (osiiChronologicalGapRightArity q.1)
              ⟨F.packetRightPositiveSource P.slope hordered x q,
                F.packetRightPositiveSource_support
                  P.slope P.slope_gt_one hordered x q⟩‖ ^ 2 ≤
            CR *
              (1 + ‖F.packetRightConfiguration
                P.slope hordered x q‖) ^
                  (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                    osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
  let leftReference :
      ℕ → SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
    fun level =>
      (((A.commonCoherentLevelFactors a level
        ).sourcewiseLocalizedFactors fs).packetLeftReference q)
  let rightReference :
      ℕ → SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
    fun level =>
      (((A.commonCoherentLevelFactors a level
        ).sourcewiseLocalizedFactors fs).packetRightReference q)
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_osiiPacketLeftPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
      OS q leftReference
        (by
          simpa [leftReference] using
            A.commonPacketAt_packetLeftReference_isVonNBounded a fs q)
  obtain ⟨CR, hCR, hright⟩ :=
    exists_osiiPacketRightPositiveCLM_norm_sq_translate_bound_uniform_family_slope_ofOS
      OS q rightReference
        (by
          simpa [rightReference] using
            A.commonPacketAt_packetRightReference_isVonNBounded a fs q)
  refine ⟨CL, CR, hCL, hCR, ?_⟩
  intro timeScale spatialLevel x
  let P := A.commonPacketAt timeScale spatialLevel
  let F := (P.levelCover.carrier a).sourcewiseLocalizedFactors fs
  let hordered :=
    (P.levelCover.carrier a).sourcewiseLocalizedFactors_axisPairOrdered
      P.slope (P.ordered a) fs
  let cL := F.packetLeftConfiguration P.slope hordered x q
  let cR := F.packetRightConfiguration P.slope hordered x q
  have heqL :
      F.packetLeftPositiveSource P.slope hordered x q =
        osiiPacketLeftPositiveCLM P.slope q
          (translateSchwartzConfiguration cL
            (leftReference spatialLevel)) := by
    simpa [P, F, leftReference, cL, commonPacketAt,
      commonCoherentLevelCover, commonCoherentLevelFactors] using
      F.packetLeftPositiveSource_eq_configurationTranslate
        P.slope hordered x q
  have heqR :
      F.packetRightPositiveSource P.slope hordered x q =
        osiiPacketRightPositiveCLM P.slope q
          (translateSchwartzConfiguration cR
            (rightReference spatialLevel)) := by
    simpa [P, F, rightReference, cR, commonPacketAt,
      commonCoherentLevelCover, commonCoherentLevelFactors] using
      F.packetRightPositiveSource_eq_configurationTranslate
        P.slope hordered x q
  have hsL :
      tsupport
          (osiiPacketLeftPositiveCLM P.slope q
              (translateSchwartzConfiguration cL
                (leftReference spatialLevel)) :
            NPointDomain d
              (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapLeftArity q.1) := by
    rw [← heqL]
    exact F.packetLeftPositiveSource_support
      P.slope P.slope_gt_one hordered x q
  have hsR :
      tsupport
          (osiiPacketRightPositiveCLM P.slope q
              (translateSchwartzConfiguration cR
                (rightReference spatialLevel)) :
            NPointDomain d
              (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
        OrderedPositiveTimeRegion d
          (osiiChronologicalGapRightArity q.1) := by
    rw [← heqR]
    exact F.packetRightPositiveSource_support
      P.slope P.slope_gt_one hordered x q
  constructor
  · let u :
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapLeftArity q.1) :=
      ⟨F.packetLeftPositiveSource P.slope hordered x q,
        F.packetLeftPositiveSource_support
          P.slope P.slope_gt_one hordered x q⟩
    let v :
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapLeftArity q.1) :=
      ⟨osiiPacketLeftPositiveCLM P.slope q
          (translateSchwartzConfiguration cL
            (leftReference spatialLevel)), hsL⟩
    have huv : u = v := by
      apply Subtype.ext
      exact heqL
    change
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapLeftArity q.1) u‖ ^ 2 ≤
        CL * (1 + ‖F.packetLeftConfiguration
          P.slope hordered x q‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1))
    calc
      _ =
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapLeftArity q.1) v‖ ^ 2 := by
        rw [huv]
      _ ≤ CL * (1 + ‖cL‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) :=
        hleft spatialLevel P.slope cL hsL
      _ =
          CL * (1 + ‖F.packetLeftConfiguration
            P.slope hordered x q‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
        rfl
  · let u :
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapRightArity q.1) :=
      ⟨F.packetRightPositiveSource P.slope hordered x q,
        F.packetRightPositiveSource_support
          P.slope P.slope_gt_one hordered x q⟩
    let v :
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapRightArity q.1) :=
      ⟨osiiPacketRightPositiveCLM P.slope q
          (translateSchwartzConfiguration cR
            (rightReference spatialLevel)), hsR⟩
    have huv : u = v := by
      apply Subtype.ext
      exact heqR
    change
      ‖osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1) u‖ ^ 2 ≤
        CR * (1 + ‖F.packetRightConfiguration
          P.slope hordered x q‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1))
    calc
      _ =
          ‖osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapRightArity q.1) v‖ ^ 2 := by
        rw [huv]
      _ ≤ CR * (1 + ‖cR‖) ^
            (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
              osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) :=
        hright spatialLevel P.slope cR hsR
      _ =
          CR * (1 + ‖F.packetRightConfiguration
            P.slope hordered x q‖) ^
              (osiiOriginalOSBoundedStateSourceOrder OS (k + 1) +
                osiiOriginalOSBoundedStateSourceOrder OS (k + 1)) := by
        rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
