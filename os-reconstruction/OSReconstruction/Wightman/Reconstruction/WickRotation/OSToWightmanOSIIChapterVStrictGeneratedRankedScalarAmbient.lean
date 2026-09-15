import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarCoefficientChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientFullTube

/-!
# Ambient continuation for one ranked scalar convexification

The rank-successor seed stage already realizes every generator, old scalar,
and vacuum-tail seed needed for the next scalar analytic rank.  Full-rank
coefficient presentations of those seeds therefore feed the common
Malgrange-Zerner coefficient engine.

This file supplies one zero-pointed ambient chart for every complex
logarithmic target whose imaginary part has rank `rank + 1`, then uses the
carrier-parametric ambient atlas to glue those charts.  The resulting stage
contains the complete logarithmic tube and retains an open predecessor germ.
-/

noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A pure-imaginary next-rank scalar target admits a zero-pointed ambient
chart over the ranked successor seed stage. -/
theorem nonempty_rankSuccessorScalarTargetAmbientChartData
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (depth + 1) x) :
    Nonempty
      (ZeroPointedAmbientChartData
        (D.next.stage k)
        (fun j => (x j : Complex) * I)) := by
  obtain ⟨n, hn, w, seed, hw, hsum_lt, hseed,
      hcombination, hsurj, hregular⟩ :=
    exists_sectionRegular_fullRank_rankSuccessorSeedCombination_fin
      hx
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let S : Real := ∑ i, w i
  let rho : Real := (S + 1) / 2
  have hS_nonneg : 0 <= S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hw i
  have hS_rho : S < rho := by
    dsimp [rho]
    linarith
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho, S]
    linarith
  let P : SCV.StripCompactificationParameters S rho :=
    Classical.choice
      (SCV.exists_stripCompactificationParameters
        hS_nonneg hS_rho)
  let B :
      StrictScalarSeedCoefficientMZBoundData
        (D.next.stage k) P seed :=
    Classical.choice
      (StrictScalarSeedCoefficientMZBoundData.nonempty
        (fun r hr =>
          D.rankSuccessorSeedCoefficientMap_mem_pullbackStage_of_mem_flat
            hseed hr)
        hrho_pos hrho_lt_one)
  let r0 : Fin n -> Complex :=
    osiiStrictScalarSeedCoefficientTarget w
  let R : StrictCoefficientTargetSectionData seed r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetSectionData
        seed r0 hsurj hregular)
  let C : StrictCoefficientTargetConvexChartData P r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetConvexChartData
        P w hw (le_refl S))
  have htarget :
      osiiStrictScalarSeedCoefficientCLM seed r0 =
        fun j => (x j : Complex) * I := by
    rw [osiiStrictScalarSeedCoefficientCLM_apply]
    exact
      osiiStrictScalarSeedCoefficientMap_target
        w seed x hcombination
  obtain ⟨U, hU_open, hU_zero, hU_subset, hU_eq⟩ :=
    R.exists_open_seed_toAmbientStage_eq_predecessor C B
  exact
    ⟨{
      stage := R.toAmbientStage C B
      carrier_convex := R.ambientDomain_convex C
      zero_mem := R.zero_mem_ambientDomain C
      target_mem := by
        rw [← htarget]
        exact R.target_mem_ambientDomain C
      seedDomain := U
      seed_open := hU_open
      zero_mem_seed := hU_zero
      seed_subset_overlap := hU_subset
      seed_agreesPredecessor := hU_eq }⟩

/-- An arbitrary complex logarithmic target over the next-rank scalar base
admits a zero-pointed ambient chart. -/
theorem nonempty_rankSuccessorScalarLogarithmicTargetAmbientChartData
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    (z : Fin k -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (depth + 1)
        (fun j => (z j).im)) :
    Nonempty
      (ZeroPointedAmbientChartData
        (D.next.stage k) z) := by
  by_cases hz0 : z = 0
  · subst z
    rw [show (0 : Fin k -> Complex) = (fun _ => 0) by
      funext j
      simp]
    simpa using
      (nonempty_rankSuccessorScalarTargetAmbientChartData
        D hz)
  let x : Fin k -> Real := fun j => (z j).im
  obtain ⟨n, hn, w, seed, hw, hsum_lt, hseed,
      hcombination, hsurj, _hregular⟩ :=
    exists_sectionRegular_fullRank_rankSuccessorSeedCombination_fin
      hz
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨v, hv⟩ :=
    exists_real_strictScalarSeedCoefficient_preimage
      seed hsurj (fun j => (z j).re)
  let r0 : Fin n -> Complex :=
    fun i => (v i : Complex) + (w i : Complex) * I
  have htarget :
      osiiStrictScalarSeedCoefficientCLM seed r0 = z := by
    rw [osiiStrictScalarSeedCoefficientCLM_apply]
    funext j
    apply Complex.ext
    · have hj :=
        congrArg Complex.re (congrFun hv j)
      simpa [osiiStrictScalarSeedCoefficientMap, r0] using hj
    · have hj := congrFun hcombination j
      simpa [osiiStrictScalarSeedCoefficientMap, r0, x,
        Finset.sum_apply, Pi.smul_apply] using hj
  let S : Real := ∑ i, w i
  let rho : Real := (S + 1) / 2
  have hS_nonneg : 0 <= S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hw i
  have hS_rho : S < rho := by
    dsimp [rho]
    linarith
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho, S]
    linarith
  have hr0_budget :
      (∑ i, |(r0 i).im|) <= S := by
    dsimp [r0, S]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _hi
    simpa using abs_of_nonneg (hw i)
  obtain ⟨P, hsegment⟩ :=
    exists_stripCompactificationParameters_segment_subset_germDomain
      r0 hS_nonneg hr0_budget hS_rho
  let B :
      StrictScalarSeedCoefficientMZBoundData
        (D.next.stage k) P seed :=
    Classical.choice
      (StrictScalarSeedCoefficientMZBoundData.nonempty
        (fun r hr =>
          D.rankSuccessorSeedCoefficientMap_mem_pullbackStage_of_mem_flat
            hseed hr)
        hrho_pos hrho_lt_one)
  have hregular :
      r0 = 0 ∨
        osiiStrictScalarSeedCoefficientMap seed r0 ≠ 0 := by
    right
    intro hzero
    apply hz0
    rw [← htarget]
    simpa [osiiStrictScalarSeedCoefficientCLM_apply] using hzero
  let R : StrictCoefficientTargetSectionData seed r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetSectionData
        seed r0 hsurj hregular)
  let C : StrictCoefficientTargetConvexChartData P r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetConvexChartData_of_segment_subset
        hsegment)
  obtain ⟨U, hU_open, hU_zero, hU_subset, hU_eq⟩ :=
    R.exists_open_seed_toAmbientStage_eq_predecessor C B
  exact
    ⟨{
      stage := R.toAmbientStage C B
      carrier_convex := R.ambientDomain_convex C
      zero_mem := R.zero_mem_ambientDomain C
      target_mem := by
        rw [← htarget]
        exact R.target_mem_ambientDomain C
      seedDomain := U
      seed_open := hU_open
      zero_mem_seed := hU_zero
      seed_subset_overlap := hU_subset
      seed_agreesPredecessor := hU_eq }⟩

/-- Complex logarithmic targets whose imaginary part belongs to the next
scalar analytic-rank stratum. -/
def RankSuccessorScalarLogarithmicTargetIndex
    (k N rank : Nat) :=
  {z : Fin k -> Complex //
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      (rank + 1) .scalar k N (fun j => (z j).im)}

namespace RankSuccessorScalarLogarithmicTargetIndex

def zero (k N rank : Nat) :
    RankSuccessorScalarLogarithmicTargetIndex k N rank :=
  ⟨0, by
    rw [show (fun j => ((0 : Fin k -> Complex) j).im) =
        (0 : Fin k -> Real) by
      funext j
      simp]
    exact
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
        (rank + 1) k N)⟩

end RankSuccessorScalarLogarithmicTargetIndex

/-- The carrier-parametric zero-pointed atlas over all next-rank complex
logarithmic targets. -/
noncomputable def rankSuccessorScalarLogarithmicTargetAmbientAtlas
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank) :
    ZeroPointedAmbientAtlasData (D.next.stage k) where
  Index :=
    RankSuccessorScalarLogarithmicTargetIndex
      k (depth + 1) rank
  target := fun a => a.1
  distinguished :=
    RankSuccessorScalarLogarithmicTargetIndex.zero
      k (depth + 1) rank
  chart := fun a =>
    Classical.choice
      (nonempty_rankSuccessorScalarLogarithmicTargetAmbientChartData
        D a.1 a.2)

/-- Glued logarithmic continuation stage covering the complete next-rank
scalar tube. -/
noncomputable def rankSuccessorScalarLogarithmicTargetAmbientStage
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank) :
    OSIITimeContinuationStage d k :=
  (rankSuccessorScalarLogarithmicTargetAmbientAtlas D).stage

theorem rankSuccessorScalarLogarithmicTarget_mem_ambientStage
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    {z : Fin k -> Complex}
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (depth + 1)
        (fun j => (z j).im)) :
    z ∈
      (rankSuccessorScalarLogarithmicTargetAmbientStage
        D).carrier := by
  let a :
      RankSuccessorScalarLogarithmicTargetIndex
        k (depth + 1) rank :=
    ⟨z, hz⟩
  exact
    (rankSuccessorScalarLogarithmicTargetAmbientAtlas D
      ).target_mem_stage a

/-- The complete additive logarithmic tube over the next-rank scalar base is
contained in the glued ambient stage. -/
theorem rankSuccessorScalarLogarithmicTube_subset_ambientStage
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank) :
    osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank
          k (depth + 1) (rank + 1)) ⊆
      (rankSuccessorScalarLogarithmicTargetAmbientStage
        D).carrier := by
  intro z hz
  exact
    rankSuccessorScalarLogarithmicTarget_mem_ambientStage
      D hz.1

/-- The ranked ambient stage retains a nonempty open zero-centered germ of
the predecessor stage. -/
theorem exists_open_seed_rankSuccessorScalarAmbientStage_eq_predecessor
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank) :
    ∃ U : Set (Fin k -> Complex),
      IsOpen U ∧ (0 : Fin k -> Complex) ∈ U ∧
      U ⊆
        (rankSuccessorScalarLogarithmicTargetAmbientStage
          D).carrier ∩
          (logarithmicPullbackStage
            (D.next.stage k)).carrier ∧
      Set.EqOn
        (rankSuccessorScalarLogarithmicTargetAmbientStage
          D).distribution
        (logarithmicPullbackStage
          (D.next.stage k)).distribution
        U :=
  (rankSuccessorScalarLogarithmicTargetAmbientAtlas
    D).exists_open_seed_stage_eq_predecessor

end OSIIChapterV
end OSReconstruction
