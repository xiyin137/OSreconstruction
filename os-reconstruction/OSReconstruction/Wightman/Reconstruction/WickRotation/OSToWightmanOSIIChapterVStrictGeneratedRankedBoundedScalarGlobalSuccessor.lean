/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarSeedCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientFullTube














noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Target-adapted exact-bound charts for every flat point of every finite
rank-successor seed family. -/
structure BoundedGlobalRankSuccessorFlatChartData
    {m : Nat} {B : Real}
    (A : BoundedScalarContinuationData m B)
    (rank depth : Nat) where
  bound_pos : 0 < B
  chart : forall
    (n : Nat)
    (seed : Fin n -> Fin m -> Real),
    (forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank m (depth + 1) (seed a)) ->
    forall {S rho : Real}
      (P : SCV.StripCompactificationParameters S rho),
      0 < rho ->
      rho < 1 ->
      (r : Fin n -> Complex) ->
      r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      BoundedScalarTargetChartData A
        (osiiStrictScalarSeedCoefficientMap seed r)

/-- Index for all target-adapted charts in the global flat atlas. -/
structure BoundedGlobalRankSuccessorFlatChartIndex
    {m : Nat}
    (rank depth : Nat) where
  coefficientBudget : Real
  windowRadius : Real
  compactification :
    SCV.StripCompactificationParameters
      coefficientBudget windowRadius
  windowRadius_pos : 0 < windowRadius
  windowRadius_lt_one : windowRadius < 1
  seedCount : Nat
  seed : Fin seedCount -> Fin m -> Real
  seed_rank : forall a,
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank m (depth + 1) (seed a)
  coefficient : Fin seedCount -> Complex
  coefficient_mem :
    coefficient ∈ osiiStrictScalarSeedCoefficientFlatWindow
      (Fin seedCount)
      (compactification.radius + windowRadius) windowRadius

namespace BoundedGlobalRankSuccessorFlatChartData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {rank depth : Nat}

/-- Constructorwise old/generator/tail producers for every finite seed
family supply the complete global flat-chart datum. -/
noncomputable def ofConstructorwise
    (hB : 0 < B)
    (produce : forall
      (n : Nat)
      (seed : Fin n -> Fin m -> Real)
      (_hseed : forall a,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank m (depth + 1) (seed a)),
      forall {S rho : Real}
        (P : SCV.StripCompactificationParameters S rho),
        0 < rho ->
        rho < 1 ->
        Nonempty
          (BoundedRankSuccessorSeedFlatChartProducerData
            A P rank (depth + 1) seed)) :
    BoundedGlobalRankSuccessorFlatChartData A rank depth where
  bound_pos := hB
  chart := by
    intro n seed hseed S rho P hrho_pos hrho_lt_one r hr
    let D := Classical.choice
      (produce n seed hseed P hrho_pos hrho_lt_one)
    exact D.targetChart r hr

/-- A harmless compactification used only to witness that the global chart
index is nonempty. -/
noncomputable def zeroCompactification :
    SCV.StripCompactificationParameters (0 : Real) (1 / 2 : Real) :=
  Classical.choice
    (SCV.exists_stripCompactificationParameters
      (by norm_num) (by norm_num))

/-- The canonical zero chart makes the global flat atlas nonempty. -/
def zeroIndex
    (_D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedGlobalRankSuccessorFlatChartIndex
      (m := m) rank depth where
  coefficientBudget := 0
  windowRadius := 1 / 2
  compactification := zeroCompactification
  windowRadius_pos := by norm_num
  windowRadius_lt_one := by norm_num
  seedCount := 1
  seed := fun _ => 0
  seed_rank := fun _ =>
    OSIIStrictGeneratedScalarRankSuccessorSeed.old
      (OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
        rank m (depth + 1))
  coefficient := 0
  coefficient_mem :=
    BoundedScalarBranchAtlasData.zero_mem_coefficientFlatWindow
      zeroCompactification (by norm_num)

/-- The exact-bound atlas containing every selected flat chart at this
analytic rank. -/
noncomputable def flatAtlas
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedScalarBranchAtlasData A where
  chart := BoundedGlobalRankSuccessorFlatChartIndex
    (m := m) rank depth
  chart_nonempty := ⟨D.zeroIndex⟩
  chartData q :=
    (D.chart q.seedCount q.seed q.seed_rank
      q.compactification q.windowRadius_pos
      q.windowRadius_lt_one q.coefficient
      q.coefficient_mem).repointZero

/-- Every finite rank-successor coefficient window is covered by the global
flat atlas. -/
theorem coefficientWindow_subset_flatAtlas
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (hrho_pos : 0 < rho)
    (hrho_lt_one : rho < 1)
    (n : Nat)
    (seed : Fin n -> Fin m -> Real)
    (hseed : forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank m (depth + 1) (seed a)) :
    osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ⊆
      osiiStrictScalarSeedCoefficientMap seed ⁻¹'
        D.flatAtlas.domain := by
  intro r hr
  apply Set.mem_iUnion.mpr
  let q : BoundedGlobalRankSuccessorFlatChartIndex
      (m := m) rank depth :=
    { coefficientBudget := S
      windowRadius := rho
      compactification := P
      windowRadius_pos := hrho_pos
      windowRadius_lt_one := hrho_lt_one
      seedCount := n
      seed := seed
      seed_rank := hseed
      coefficient := r
      coefficient_mem := hr }
  exact
    ⟨q, (D.chart n seed hseed P hrho_pos hrho_lt_one
      r hr).target_mem_domain⟩

/-- The global flat atlas supplies the branch input for every finite
rank-successor presentation. -/
noncomputable def seedBranchInput
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (hrho_pos : 0 < rho)
    (hrho_lt_one : rho < 1)
    (n : Nat) (_hn : 0 < n)
    (weight : Fin n -> Real)
    (seed : Fin n -> Fin m -> Real)
    (hseed : forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank m (depth + 1) (seed a)) :
    BoundedStrictScalarSeedBranchInputData A P seed weight := by
  letI : NeZero n := ⟨Nat.ne_of_gt _hn⟩
  exact D.flatAtlas.toSeedBranchInput P seed weight
    (D.coefficientWindow_subset_flatAtlas
      P hrho_pos hrho_lt_one n seed hseed)

/-- Every next-rank target has an ordinary bounded coefficient successor
package built from the one global flat atlas. -/
theorem nonempty_rankTargetData
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (target : Fin m -> Real)
    (htarget :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) target) :
    Nonempty
      (BoundedStrictGeneratedScalarRankSuccessorData
        A rank depth target) := by
  apply BoundedStrictGeneratedScalarRankSuccessorData.nonempty_of_target
    A rank depth target D.bound_pos htarget
  intro n hn weight seed _hweight _hsum hseed _hcombination
      _hsurjective _hregular rho P hrho_pos hrho_lt_one
  exact
    ⟨D.seedBranchInput P hrho_pos hrho_lt_one
      n hn weight seed hseed⟩

/-- Select the ordinary finite coefficient successor for one next-rank
target. -/
noncomputable def rankTargetData
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (target : Fin m -> Real)
    (htarget :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) target) :
    BoundedStrictGeneratedScalarRankSuccessorData
      A rank depth target :=
  Classical.choice (D.nonempty_rankTargetData target htarget)

/-- The selected coefficient chart, retargeted to the requested
pure-imaginary ambient point. -/
noncomputable def rankTargetChart
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (target : Fin m -> Real)
    (htarget :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) target) :
    BoundedScalarTargetChartData A
      (fun j => (target j : Complex) * I) := by
  let R := D.rankTargetData target htarget
  rw [← R.coefficientTarget_eq]
  exact R.targetChart

/-- Every complex logarithmic target whose imaginary part has the next
analytic rank admits an exact-bound chart.  A full-rank seed presentation
absorbs the arbitrary real center, while the same compactified MZ extension
used on the flat cross is retargeted along the complete coefficient segment.
-/
theorem nonempty_logarithmicRankTargetChart
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (z : Fin m -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) (fun j => (z j).im)) :
    Nonempty (BoundedScalarTargetChartData A z) := by
  by_cases hz0 : z = 0
  · subst z
    have hzero :
        OSIIStrictGeneratedLogarithmicArgumentAtRank
          (rank + 1) .scalar m (depth + 1) 0 :=
      OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
        (rank + 1) m (depth + 1)
    refine ⟨?_⟩
    convert D.rankTargetChart 0 hzero using 1
    funext j
    simp
  obtain ⟨n, hn, weight, seed, hweight, hsum, hseed,
      hcombination, hsurjective, _hregular⟩ :=
    exists_sectionRegular_fullRank_rankSuccessorSeedCombination_fin hz
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨v, hv⟩ :=
    exists_real_strictScalarSeedCoefficient_preimage
      seed hsurjective (fun j => (z j).re)
  let r0 : Fin n -> Complex :=
    fun i => (v i : Complex) + (weight i : Complex) * I
  have htarget :
      osiiStrictScalarSeedCoefficientCLM seed r0 = z := by
    rw [osiiStrictScalarSeedCoefficientCLM_apply]
    funext j
    apply Complex.ext
    · have hj := congrArg Complex.re (congrFun hv j)
      simpa [osiiStrictScalarSeedCoefficientMap, r0] using hj
    · have hj := congrFun hcombination j
      simpa [osiiStrictScalarSeedCoefficientMap, r0,
        Finset.sum_apply, Pi.smul_apply] using hj
  let S : Real := ∑ i, weight i
  let rho : Real := (S + 1) / 2
  have hS_nonneg : 0 <= S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hweight i
  have hS_rho : S < rho := by
    dsimp [rho]
    linarith
  have hrho_pos : 0 < rho := hS_nonneg.trans_lt hS_rho
  have hrho_lt_one : rho < 1 := by
    dsimp [rho, S]
    linarith
  have hr0_budget :
      (∑ i, |(r0 i).im|) <= S := by
    dsimp [r0, S]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _hi
    simpa using abs_of_nonneg (hweight i)
  obtain ⟨P, hsegment⟩ :=
    exists_stripCompactificationParameters_segment_subset_germDomain
      r0 hS_nonneg hr0_budget hS_rho
  let branchInput :=
    D.seedBranchInput P hrho_pos hrho_lt_one
      n hn weight seed hseed
  let C : BoundedStrictScalarSeedCoefficientChartData
      P branchInput.branch seed weight B :=
    Classical.choice
      (BoundedStrictScalarSeedCoefficientChartData.nonempty_of_window
        P branchInput.branch branchInput.domain seed
        branchInput.branch_differentiableOn
        branchInput.coefficientWindow_subset hrho_pos
        weight hweight (le_refl S) B D.bound_pos
        branchInput.norm_branch_le)
  let Q : StrictCoefficientTargetConvexChartData P r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetConvexChartData_of_segment_subset
        hsegment)
  have hregular :
      r0 = 0 ∨ osiiStrictScalarSeedCoefficientMap seed r0 ≠ 0 := by
    right
    intro hzero
    apply hz0
    rw [← htarget, osiiStrictScalarSeedCoefficientCLM_apply]
    exact hzero
  let R : StrictCoefficientTargetSectionData seed r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetSectionData
        seed r0 hsurjective hregular)
  have hlocal :=
    BoundedScalarTargetChartData.germ_eq_predecessor_on_ball_of_real
      C branchInput.agreementRadius
      branchInput.agreementRadius_pos
      branchInput.agreementBall_subset
      branchInput.realAgreement
  let chart :=
    BoundedScalarTargetChartData.ofCoefficientLocalAgreementAt
      C Q R branchInput.agreementRadius
      branchInput.agreementRadius_pos
      branchInput.agreementBall_subset hlocal
  rw [htarget] at chart
  exact ⟨chart⟩

/-- Select the exact-bound chart at one arbitrary logarithmic point of the
next scalar rank. -/
noncomputable def logarithmicRankTargetChart
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (z : Fin m -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) (fun j => (z j).im)) :
    BoundedScalarTargetChartData A z :=
  Classical.choice (D.nonempty_logarithmicRankTargetChart z hz)

/-- Retain all global flat charts before adjoining every next-rank target. -/
noncomputable def flatSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedScalarContinuationData m B :=
  D.flatAtlas.toSuccessor

/-- Rebase one next-rank target chart onto the flat-atlas successor. -/
noncomputable def retainedRankTargetChart
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (target : Fin m -> Real)
    (htarget :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) target) :
    BoundedScalarTargetChartData D.flatSuccessor
      (fun j => (target j : Complex) * I) :=
  (D.rankTargetChart target htarget).rebase
    D.flatAtlas.predecessor_subset_toSuccessor
    D.flatAtlas.toSuccessor_eq_predecessor

/-- Rebase one arbitrary next-rank logarithmic target chart onto the
flat-atlas successor. -/
noncomputable def retainedLogarithmicRankTargetChart
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (z : Fin m -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) (fun j => (z j).im)) :
    BoundedScalarTargetChartData D.flatSuccessor z :=
  (D.logarithmicRankTargetChart z hz).rebase
    D.flatAtlas.predecessor_subset_toSuccessor
    D.flatAtlas.toSuccessor_eq_predecessor

end BoundedGlobalRankSuccessorFlatChartData

/-- One complex target whose imaginary part lies in a scalar rank
stratum. -/
structure BoundedScalarLogarithmicRankTargetIndex
    (rank m depth : Nat) where
  target : Fin m -> Complex
  target_mem :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar m depth (fun j => (target j).im)

namespace BoundedGlobalRankSuccessorFlatChartData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {rank depth : Nat}

/-- All complex logarithmic targets over the next-rank imaginary stratum
form one coherent exact-bound atlas over the flat-atlas successor. -/
noncomputable def logarithmicRankTargetAtlas
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedScalarBranchAtlasData D.flatSuccessor where
  chart :=
    BoundedScalarLogarithmicRankTargetIndex
      (rank + 1) m (depth + 1)
  chart_nonempty := ⟨{
    target := 0
    target_mem := by
      convert
        (OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
          (rank + 1) m (depth + 1)) using 1
      funext j
      rfl }⟩
  chartData q :=
    (D.retainedLogarithmicRankTargetChart
      q.target q.target_mem).repointZero

/-- The complete exact-bound successor for one analytic rank. -/
noncomputable def rankSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedScalarContinuationData m B :=
  D.logarithmicRankTargetAtlas.toSuccessor

theorem predecessor_subset_rankSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    A.carrier ⊆ D.rankSuccessor.carrier :=
  D.flatAtlas.predecessor_subset_toSuccessor.trans
    D.logarithmicRankTargetAtlas.predecessor_subset_toSuccessor

/-- The global rank successor agrees with its predecessor on the complete
old carrier. -/
theorem rankSuccessor_eq_predecessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    Set.EqOn D.rankSuccessor.toFun A.toFun A.carrier := by
  intro z hz
  exact
    (D.logarithmicRankTargetAtlas.toSuccessor_eq_predecessor
      (D.flatAtlas.predecessor_subset_toSuccessor hz)).trans
        (D.flatAtlas.toSuccessor_eq_predecessor hz)

/-- Every complex logarithmic target over the next-rank scalar stratum
belongs to the global exact-bound successor. -/
theorem logarithmicRankTarget_mem_rankSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (z : Fin m -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) (fun j => (z j).im)) :
    z ∈ D.rankSuccessor.carrier := by
  apply D.logarithmicRankTargetAtlas.domain_subset_toSuccessor
  apply Set.mem_iUnion.mpr
  let q :
      BoundedScalarLogarithmicRankTargetIndex
        (rank + 1) m (depth + 1) :=
    { target := z, target_mem := hz }
  exact
    ⟨q,
      (D.retainedLogarithmicRankTargetChart z hz).target_mem_domain⟩

end BoundedGlobalRankSuccessorFlatChartData
end OSIIChapterV
end OSReconstruction
