/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarCoefficientChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientBoundedBranchSuccessor













noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Analytic realization of one selected finite seed family on the compact
coefficient window sampled by strip compactification. -/
structure BoundedStrictScalarSeedBranchInputData
    {m n : Nat} {B S rho : Real}
    (A : BoundedScalarContinuationData m B)
    (P : SCV.StripCompactificationParameters S rho)
    (seed : Fin n -> Fin m -> Real)
    (weight : Fin n -> Real) where
  branch : (Fin m -> Complex) -> Complex
  domain : Set (Fin m -> Complex)
  branch_differentiableOn : DifferentiableOn Complex branch domain
  coefficientWindow_subset :
    osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ⊆
      osiiStrictScalarSeedCoefficientMap seed ⁻¹' domain
  norm_branch_le : forall r,
    r ∈ osiiStrictScalarSeedCoefficientFlatWindow
        (Fin n) (P.radius + rho) rho ->
      ‖branch (osiiStrictScalarSeedCoefficientMap seed r)‖ <= B
  agreementRadius : Real
  agreementRadius_pos : 0 < agreementRadius
  agreementBall_subset :
    Metric.ball (0 : Fin n -> Complex) agreementRadius ⊆
      osiiStrictCoefficientGermDomain P ∩
        osiiStrictScalarSeedCoefficientMap seed ⁻¹' A.carrier
  realAgreement : forall x : Fin n -> Real,
    (fun i => (x i : Complex)) ∈
        Metric.ball (0 : Fin n -> Complex) agreementRadius ->
      branch (osiiStrictScalarSeedCoefficientMap seed
          (fun i => (x i : Complex))) =
        A.toFun (osiiStrictScalarSeedCoefficientMap seed
          (fun i => (x i : Complex)))

/-- Complete finite input for one bounded passage from scalar rank `rank` to
rank `rank + 1` at target depth `depth + 1`. -/
structure BoundedStrictGeneratedScalarRankSuccessorData
    {m : Nat} {B : Real}
    (A : BoundedScalarContinuationData m B)
    (rank depth : Nat)
    (target : Fin m -> Real) where
  seedCount : Nat
  seedCount_pos : 0 < seedCount
  weight : Fin seedCount -> Real
  seed : Fin seedCount -> Fin m -> Real
  weight_nonneg : forall i, 0 <= weight i
  weight_sum_lt_one : (∑ i, weight i) < 1
  seed_rank : forall i,
    OSIIStrictGeneratedScalarRankSuccessorSeed
      rank m (depth + 1) (seed i)
  combination_eq : (∑ i, weight i • seed i) = target
  coefficient_surjective : Function.Surjective
    (osiiStrictScalarSeedCoefficientMap seed)
  target_regular :
    osiiStrictScalarSeedCoefficientTarget weight = 0 ∨
      osiiStrictScalarSeedCoefficientMap seed
          (osiiStrictScalarSeedCoefficientTarget weight) ≠ 0
  coefficientBudget : Real
  windowRadius : Real
  compactification :
    SCV.StripCompactificationParameters
      coefficientBudget windowRadius
  weight_sum_le_budget :
    (∑ i, weight i) <= coefficientBudget
  windowRadius_pos : 0 < windowRadius
  windowRadius_lt_one : windowRadius < 1
  bound_pos : 0 < B
  branchInput :
    BoundedStrictScalarSeedBranchInputData
      A compactification seed weight

namespace BoundedStrictGeneratedScalarRankSuccessorData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {rank depth : Nat} {target : Fin m -> Real}

/-- Select the bounded compactified coefficient chart. -/
noncomputable def coefficientChart
    (D : BoundedStrictGeneratedScalarRankSuccessorData
      A rank depth target) :
    letI : NeZero D.seedCount := ⟨Nat.ne_of_gt D.seedCount_pos⟩
    BoundedStrictScalarSeedCoefficientChartData
      D.compactification D.branchInput.branch D.seed D.weight B := by
  letI : NeZero D.seedCount := ⟨Nat.ne_of_gt D.seedCount_pos⟩
  exact Classical.choice
    (BoundedStrictScalarSeedCoefficientChartData.nonempty_of_window
      D.compactification D.branchInput.branch D.branchInput.domain D.seed
      D.branchInput.branch_differentiableOn
      D.branchInput.coefficientWindow_subset D.windowRadius_pos
      D.weight D.weight_nonneg D.weight_sum_le_budget B D.bound_pos
      D.branchInput.norm_branch_le)

/-- Select the continuous linear right inverse fixing the prescribed target
coefficient vector. -/
noncomputable def targetSection
    (D : BoundedStrictGeneratedScalarRankSuccessorData
      A rank depth target) :
    StrictCoefficientTargetSectionData D.seed
      (osiiStrictScalarSeedCoefficientTarget D.weight) := by
  exact Classical.choice
    (nonempty_strictCoefficientTargetSectionData
      D.seed (osiiStrictScalarSeedCoefficientTarget D.weight)
      D.coefficient_surjective D.target_regular)

/-- The bounded ambient chart obtained from real-germ agreement with the
predecessor. -/
noncomputable def targetChart
    (D : BoundedStrictGeneratedScalarRankSuccessorData
      A rank depth target) :
    BoundedScalarTargetChartData A
      (osiiStrictScalarSeedCoefficientCLM D.seed
        (osiiStrictScalarSeedCoefficientTarget D.weight)) := by
  letI : NeZero D.seedCount := ⟨Nat.ne_of_gt D.seedCount_pos⟩
  let C : BoundedStrictScalarSeedCoefficientChartData
      D.compactification D.branchInput.branch D.seed D.weight B :=
    Classical.choice
      (BoundedStrictScalarSeedCoefficientChartData.nonempty_of_window
        D.compactification D.branchInput.branch D.branchInput.domain D.seed
        D.branchInput.branch_differentiableOn
        D.branchInput.coefficientWindow_subset D.windowRadius_pos
        D.weight D.weight_nonneg D.weight_sum_le_budget B D.bound_pos
        D.branchInput.norm_branch_le)
  have hlocal :=
    BoundedScalarTargetChartData.germ_eq_predecessor_on_ball_of_real
      C D.branchInput.agreementRadius
      D.branchInput.agreementRadius_pos
      D.branchInput.agreementBall_subset
      D.branchInput.realAgreement
  exact
    BoundedScalarTargetChartData.ofCoefficientLocalAgreement
      C D.targetSection D.branchInput.agreementRadius
      D.branchInput.agreementRadius_pos
      D.branchInput.agreementBall_subset hlocal

/-- The selected ambient coefficient target is exactly the pure-imaginary
embedding of the requested real logarithmic argument. -/
theorem coefficientTarget_eq
    (D : BoundedStrictGeneratedScalarRankSuccessorData
      A rank depth target) :
    osiiStrictScalarSeedCoefficientCLM D.seed
        (osiiStrictScalarSeedCoefficientTarget D.weight) =
      fun j => (target j : Complex) * I := by
  rw [osiiStrictScalarSeedCoefficientCLM_apply]
  exact
    osiiStrictScalarSeedCoefficientMap_target
      D.weight D.seed target D.combination_eq

/-- A branch producer for every finite presentation constructs the complete
bounded rank successor for any next-rank target. -/
theorem nonempty_of_target
    (A : BoundedScalarContinuationData m B)
    (rank depth : Nat)
    (target : Fin m -> Real)
    (hB : 0 < B)
    (htarget :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) target)
    (realize : forall
      (n : Nat) (_hn : 0 < n)
      (weight : Fin n -> Real)
      (seed : Fin n -> Fin m -> Real),
      (forall i, 0 <= weight i) ->
      (∑ i, weight i) < 1 ->
      (forall i,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank m (depth + 1) (seed i)) ->
      (∑ i, weight i • seed i) = target ->
      Function.Surjective
        (osiiStrictScalarSeedCoefficientMap seed) ->
      (osiiStrictScalarSeedCoefficientTarget weight = 0 ∨
        osiiStrictScalarSeedCoefficientMap seed
            (osiiStrictScalarSeedCoefficientTarget weight) ≠ 0) ->
      forall (rho : Real)
        (P : SCV.StripCompactificationParameters
          (∑ i, weight i) rho),
        0 < rho ->
        rho < 1 ->
        Nonempty
          (BoundedStrictScalarSeedBranchInputData A P seed weight)) :
    Nonempty
      (BoundedStrictGeneratedScalarRankSuccessorData
        A rank depth target) := by
  obtain ⟨n, hn, weight, seed, hweight, hsum, hseed,
      hcombination, hsurjective, hregular⟩ :=
    exists_sectionRegular_fullRank_rankSuccessorSeedCombination_fin htarget
  let S : Real := ∑ i, weight i
  let rho : Real := (S + 1) / 2
  have hS_nonneg : 0 <= S :=
    Finset.sum_nonneg fun i _ => hweight i
  have hS_rho : S < rho := by
    dsimp [rho]
    linarith
  have hrho_pos : 0 < rho := hS_nonneg.trans_lt hS_rho
  have hrho_lt_one : rho < 1 := by
    dsimp [rho, S]
    linarith
  let P : SCV.StripCompactificationParameters S rho :=
    Classical.choice
      (SCV.exists_stripCompactificationParameters
        hS_nonneg hS_rho)
  obtain ⟨branch⟩ :=
    realize n hn weight seed hweight hsum hseed hcombination
      hsurjective hregular rho P hrho_pos hrho_lt_one
  exact ⟨{
    seedCount := n
    seedCount_pos := hn
    weight := weight
    seed := seed
    weight_nonneg := hweight
    weight_sum_lt_one := hsum
    seed_rank := hseed
    combination_eq := hcombination
    coefficient_surjective := hsurjective
    target_regular := hregular
    coefficientBudget := S
    windowRadius := rho
    compactification := P
    weight_sum_le_budget := by rfl
    windowRadius_pos := hrho_pos
    windowRadius_lt_one := hrho_lt_one
    bound_pos := hB
    branchInput := branch }⟩

end BoundedStrictGeneratedScalarRankSuccessorData
end OSIIChapterV
end OSReconstruction
