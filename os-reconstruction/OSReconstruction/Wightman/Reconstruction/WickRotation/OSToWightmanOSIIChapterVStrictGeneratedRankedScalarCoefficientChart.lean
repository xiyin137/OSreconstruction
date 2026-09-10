import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedOpenBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarSeedStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientFullRank

/-!
# Coefficient charts for ranked strict-generated scalar successors

The scalar rank step has the same finite-dimensional coefficient geometry as
the unranked strict-generated closure.  Its seed family is coordinatewise
solid, every next-rank target is a strict subunit finite combination of those
seeds, and bridge-only generators span every logarithmic coordinate.

This file records the ranked input expected by the common coefficient/MZ
continuation engine.
-/

noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A finite rank-successor seed family spans every real logarithmic
direction. -/
theorem exists_fin_rankSuccessorSeed_span_eq_top
    (rank k N : Nat) :
    ∃ n : Nat, ∃ seed : Fin n -> Fin k -> Real,
      (forall i,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank k (N + 1) (seed i)) ∧
      Submodule.span Real (Set.range seed) =
        (⊤ : Submodule Real (Fin k -> Real)) := by
  let seed : Fin k -> Fin k -> Real :=
    fun i => (Pi.single i (1 : Real) : Fin k -> Real)
  refine ⟨k, seed, ?_, ?_⟩
  · intro i
    simpa [seed] using
      (strictGeneratedScalarRankSuccessorSeed_piSingle
        rank k N i 1 (by
          rw [abs_one]
          nlinarith [Real.pi_gt_three]))
  · rw [eq_top_iff]
    intro x _hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _hi
    have hsingle_x :
        Pi.single i (x i) =
          x i • seed i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [seed]
      · simp [seed, hji]
    rw [hsingle_x]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, rfl⟩

/-- A finite rank-successor seed family gives a surjective complex
coefficient chart. -/
theorem exists_surjective_rankSuccessorSeedCoefficientMap
    (rank k N : Nat) :
    ∃ n : Nat, ∃ seed : Fin n -> Fin k -> Real,
      (forall i,
        OSIIStrictGeneratedScalarRankSuccessorSeed
          rank k (N + 1) (seed i)) ∧
      Function.Surjective
        (osiiStrictScalarSeedCoefficientMap seed) := by
  obtain ⟨n, seed, hseed, hspan⟩ :=
    exists_fin_rankSuccessorSeed_span_eq_top rank k N
  exact
    ⟨n, seed, hseed,
      osiiStrictScalarSeedCoefficientMap_surjective_of_span_eq_top
        seed hspan⟩

/-- A one-coordinate coefficient strip maps into the logarithmic tube over
the ranked successor seed base. -/
theorem
    osiiStrictScalarSeedCoefficientMap_mem_rankSuccessorSeedTube_of_mem_flat
    {ι : Type} [Fintype ι]
    {rank k N : Nat}
    {seed : ι -> Fin k -> Real}
    (hseed : forall i,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N (seed i))
    {r : ι -> Complex}
    (hr :
      (fun i => (r i).im) ∈
        fintypeFlatImaginaryUnion ι 1) :
    osiiStrictScalarSeedCoefficientMap seed r ∈
      osiiLogarithmicTube
        (osiiStrictGeneratedScalarRankSuccessorSeedBase
          k N rank) := by
  obtain ⟨q, hq, hzero⟩ := hr
  let y : Fin k -> Real :=
    fun j => (osiiStrictScalarSeedCoefficientMap seed r j).im
  have hy_eq : y = (r q).im • seed q := by
    rw [show y =
        ∑ i, (r i).im • seed i by
      exact osiiStrictScalarSeedCoefficientMap_im seed r]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_eq_single q ?_ ?_
    · intro p _ hp
      have hpzero : (r p).im = 0 := hzero p hp
      rw [hpzero]
      simp
    · intro hq_not
      simp at hq_not
  have hy_seed :
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k N y := by
    apply (hseed q).coordinatewiseShrink y
    intro j
    rw [hy_eq, Pi.smul_apply]
    change |(r q).im * seed q j| <= |seed q j|
    rw [abs_mul]
    calc
      |(r q).im| * |seed q j| <=
          1 * |seed q j| :=
        mul_le_mul_of_nonneg_right hq.le (abs_nonneg _)
      _ = |seed q j| := one_mul _
  rw [osiiLogarithmicTube, SCV.TubeDomain,
    osiiPhysicalLogarithmicBase]
  change y ∈
    osiiStrictGeneratedScalarRankSuccessorSeedBase
        k N rank ∩
      osiiOpenArgumentStrip k
  exact
    ⟨hy_seed,
      (hy_seed.toRankSucc.toStrictGenerated
        ).coordinate_abs_lt_pi_div_two⟩

namespace StrictGeneratedScalarRankSuccessorSeedStageLevelData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth rank : Nat}

/-- Every flat coefficient point maps into the logarithmic pullback of the
stage which realizes the ranked successor seed base. -/
theorem rankSuccessorSeedCoefficientMap_mem_pullbackStage_of_mem_flat
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    {ι : Type} [Fintype ι]
    {k : Nat}
    {seed : ι -> Fin k -> Real}
    (hseed : forall i,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank k (depth + 1) (seed i))
    {r : ι -> Complex}
    (hr :
      (fun i => (r i).im) ∈
        fintypeFlatImaginaryUnion ι 1) :
    osiiStrictScalarSeedCoefficientMap seed r ∈
      (logarithmicPullbackStage (D.next.stage k)).carrier := by
  apply
    osiiLogarithmicTube_subset_pullbackStage
      (D.scalarRankSuccessorSeedCarrier_subset k)
  exact
    osiiStrictScalarSeedCoefficientMap_mem_rankSuccessorSeedTube_of_mem_flat
      hseed hr

end StrictGeneratedScalarRankSuccessorSeedStageLevelData

/-- Every next-rank scalar target at positive depth admits a positive finite
subunit representation whose coefficient map is surjective. Extra spanning
seeds carry zero target weight. -/
theorem exists_fullRank_rankSuccessorSeedCombination_fin
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (N + 1) x) :
    ∃ n : Nat, 0 < n ∧
      ∃ (w : Fin n -> Real)
        (seed : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) < 1 ∧
        (forall i,
          OSIIStrictGeneratedScalarRankSuccessorSeed
            rank k (N + 1) (seed i)) ∧
        (∑ i, w i • seed i) = x ∧
        Function.Surjective
          (osiiStrictScalarSeedCoefficientMap seed) := by
  obtain ⟨n₁, hn₁, _hn₁_le, w₁, seed₁,
      hw₁, hsum₁, hseed₁, hcombination₁⟩ :=
    exists_rankSuccessorSeedCombination_fin hx
  obtain ⟨n₂, seed₂, hseed₂, hsurj₂⟩ :=
    exists_surjective_rankSuccessorSeedCoefficientMap
      rank k N
  let w : Fin (n₁ + n₂) -> Real :=
    Fin.append w₁ (fun _ : Fin n₂ => 0)
  let seed : Fin (n₁ + n₂) -> Fin k -> Real :=
    Fin.append seed₁ seed₂
  refine
    ⟨n₁ + n₂, Nat.lt_add_right n₂ hn₁,
      w, seed, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i =>
        simpa [w] using hw₁ i
    | right i =>
        simp [w]
  · simpa [w, Fin.sum_univ_add] using hsum₁
  · intro i
    induction i using Fin.addCases with
    | left i =>
        simpa [seed] using hseed₁ i
    | right i =>
        simpa [seed] using hseed₂ i
  · simpa [w, seed, Fin.sum_univ_add] using hcombination₁
  · exact
      osiiStrictScalarSeedCoefficientMap_append_surjective
        seed₁ seed₂ hsurj₂

/-- Full-rank ranked target presentations can be chosen compatible with a
linear target-fixing section. -/
theorem exists_sectionRegular_fullRank_rankSuccessorSeedCombination_fin
    {rank k N : Nat} {x : Fin k -> Real}
    (hx :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar k (N + 1) x) :
    ∃ n : Nat, 0 < n ∧
      ∃ (w : Fin n -> Real)
        (seed : Fin n -> Fin k -> Real),
        (forall i, 0 <= w i) ∧
        (∑ i, w i) < 1 ∧
        (forall i,
          OSIIStrictGeneratedScalarRankSuccessorSeed
            rank k (N + 1) (seed i)) ∧
        (∑ i, w i • seed i) = x ∧
        Function.Surjective
          (osiiStrictScalarSeedCoefficientMap seed) ∧
        (osiiStrictScalarSeedCoefficientTarget w = 0 ∨
          osiiStrictScalarSeedCoefficientMap seed
              (osiiStrictScalarSeedCoefficientTarget w) ≠
            0) := by
  obtain ⟨n, hn, w0, seed, hw0, hsum0, hseed,
      hcombination0, hsurj⟩ :=
    exists_fullRank_rankSuccessorSeedCombination_fin hx
  by_cases hx0 : x = 0
  · let w : Fin n -> Real := 0
    refine
      ⟨n, hn, w, seed, ?_, ?_, hseed, ?_, hsurj, Or.inl ?_⟩
    · intro i
      simp [w]
    · simp [w]
    · simpa [w, hx0]
    · ext i
      simp [w, osiiStrictScalarSeedCoefficientTarget]
  · refine
      ⟨n, hn, w0, seed, hw0, hsum0, hseed,
        hcombination0, hsurj, Or.inr ?_⟩
    have hmap :
        osiiStrictScalarSeedCoefficientMap seed
            (osiiStrictScalarSeedCoefficientTarget w0) =
          fun j => (x j : Complex) * I :=
      osiiStrictScalarSeedCoefficientMap_target
        w0 seed x hcombination0
    intro hzero
    apply hx0
    funext j
    have hj :=
      congrArg Complex.im
        (congrFun (hmap.symm.trans hzero) j)
    simpa using hj

end OSIIChapterV
end OSReconstruction
