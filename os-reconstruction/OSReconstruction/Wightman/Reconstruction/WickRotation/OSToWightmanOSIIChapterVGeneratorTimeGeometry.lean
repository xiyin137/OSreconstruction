/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSourceComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalSource










noncomputable section

open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The change in the two block time profiles induced by one real generator
parameter.  The zeroth absolute-time coordinate of each block stays fixed;
the remaining coordinates move by the left/right field parameters. -/
def generatorBlockTimeDisplacement
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    Fin (i.n + i.m) → ℝ :=
  Fin.append
    (fun a =>
      -chronologicalTimeProfileDisplacementOfPositive
        i.hn (i.leftRealCoordinates τ) a)
    (fun b =>
      -chronologicalTimeProfileDisplacementOfPositive
        i.hm (i.rightRealCoordinates τ) b)

@[simp] theorem generatorBlockTimeDisplacement_left_zero
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    generatorBlockTimeDisplacement i τ
        (Fin.castAdd i.m (⟨0, i.hn⟩ : Fin i.n)) = 0 := by
  rw [generatorBlockTimeDisplacement, Fin.append_left]
  unfold chronologicalTimeProfileDisplacementOfPositive
  simp

@[simp] theorem generatorBlockTimeDisplacement_left_succ
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (a : Fin (i.n - 1)) :
    generatorBlockTimeDisplacement i τ
        (Fin.castAdd i.m
          (Fin.cast (Nat.sub_add_cancel i.hn) a.succ)) =
      -τ (i.leftGlobalIndex a) := by
  simp [generatorBlockTimeDisplacement,
    chronologicalTimeProfileDisplacementOfPositive,
    GeneratorIndex.leftRealCoordinates]

@[simp] theorem generatorBlockTimeDisplacement_right_zero
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    generatorBlockTimeDisplacement i τ
        (Fin.natAdd i.n (⟨0, i.hm⟩ : Fin i.m)) = 0 := by
  rw [generatorBlockTimeDisplacement, Fin.append_right]
  unfold chronologicalTimeProfileDisplacementOfPositive
  simp

@[simp] theorem generatorBlockTimeDisplacement_right_succ
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ)
    (b : Fin (i.m - 1)) :
    generatorBlockTimeDisplacement i τ
        (Fin.natAdd i.n
          (Fin.cast (Nat.sub_add_cancel i.hm) b.succ)) =
      τ (i.rightGlobalIndex b) := by
  simp [generatorBlockTimeDisplacement,
    chronologicalTimeProfileDisplacementOfPositive,
    GeneratorIndex.rightRealCoordinates]

/-- The global difference-time displacement actually induced by a generator
parameter. The first coordinate is a common translation. Reflected-left gaps
move with the opposite sign, while the bridge and right gaps move with the
generator sign. -/
def generatorGlobalTimeDisplacement
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    Fin (i.n + i.m) → ℝ :=
  fun c =>
    Fin.cases
      (∑ a : Fin (i.n - 1), τ (i.leftGlobalIndex a))
      (fun j =>
        if j.val < i.bridgeGlobalIndex.val then -τ j else τ j)
      (Fin.cast i.pointArity_add c)

/-- Convert one common chronological physical-gap vector to the generator
parameter used by a particular split. Reflected-left coordinates change sign;
the bridge and right coordinates do not. -/
def generatorChronologicalParameter
    {k : ℕ}
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    Fin k → ℝ :=
  fun j =>
    if j.val < i.bridgeGlobalIndex.val then -ξ j else ξ j

/-- The common full difference-time point with a chosen zeroth coordinate and
the physical chronological gaps in the remaining coordinates. -/
def generatorPhysicalTimePoint
    {k : ℕ}
    (t₀ : ℝ)
    (ξ : Fin k → ℝ) :
    Fin (k + 1) → ℝ :=
  Fin.cases t₀ ξ

/-- The split-dependent common translation which compensates for reflection
of the left block and places the zeroth global difference coordinate at
`t₀`. -/
def generatorChronologicalCommonShift
    {k : ℕ}
    (i : GeneratorIndex k)
    (t₀ : ℝ)
    (ξ : Fin k → ℝ) : ℝ :=
  t₀ + ∑ a : Fin (i.n - 1), ξ (i.leftGlobalIndex a)

theorem GeneratorIndex.leftGlobalIndex_lt_bridgeGlobalIndex
    {k : ℕ}
    (i : GeneratorIndex k)
    (a : Fin (i.n - 1)) :
    (i.leftGlobalIndex a).val < i.bridgeGlobalIndex.val := by
  change (Fin.rev a).val < i.n - 1
  exact (Fin.rev a).isLt

theorem GeneratorIndex.bridgeGlobalIndex_not_lt_self
    {k : ℕ}
    (i : GeneratorIndex k) :
    ¬i.bridgeGlobalIndex.val < i.bridgeGlobalIndex.val :=
  lt_irrefl _

theorem GeneratorIndex.not_rightGlobalIndex_lt_bridgeGlobalIndex
    {k : ℕ}
    (i : GeneratorIndex k)
    (b : Fin (i.m - 1)) :
    ¬(i.rightGlobalIndex b).val < i.bridgeGlobalIndex.val := by
  simp [GeneratorIndex.rightGlobalIndex,
    GeneratorIndex.bridgeGlobalIndex]
  omega

@[simp] theorem generatorChronologicalParameter_left
    {k : ℕ}
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ)
    (a : Fin (i.n - 1)) :
    generatorChronologicalParameter i ξ (i.leftGlobalIndex a) =
      -ξ (i.leftGlobalIndex a) := by
  rw [generatorChronologicalParameter, if_pos]
  exact i.leftGlobalIndex_lt_bridgeGlobalIndex a

@[simp] theorem generatorChronologicalParameter_bridge
    {k : ℕ}
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    generatorChronologicalParameter i ξ i.bridgeGlobalIndex =
      ξ i.bridgeGlobalIndex := by
  rw [generatorChronologicalParameter, if_neg]
  exact i.bridgeGlobalIndex_not_lt_self

@[simp] theorem generatorChronologicalParameter_right
    {k : ℕ}
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ)
    (b : Fin (i.m - 1)) :
    generatorChronologicalParameter i ξ (i.rightGlobalIndex b) =
      ξ (i.rightGlobalIndex b) := by
  rw [generatorChronologicalParameter, if_neg]
  exact i.not_rightGlobalIndex_lt_bridgeGlobalIndex b

@[simp] theorem generatorPhysicalTimePoint_zero
    {k : ℕ}
    (t₀ : ℝ)
    (ξ : Fin k → ℝ) :
    generatorPhysicalTimePoint t₀ ξ 0 = t₀ := by
  simp [generatorPhysicalTimePoint]

@[simp] theorem generatorPhysicalTimePoint_succ
    {k : ℕ}
    (t₀ : ℝ)
    (ξ : Fin k → ℝ)
    (j : Fin k) :
    generatorPhysicalTimePoint t₀ ξ j.succ = ξ j := by
  simp [generatorPhysicalTimePoint]

private theorem section43ScalarDiffCLE_symm_cast_succ_sub_cast_castSucc
    {n : ℕ}
    (hn : 0 < n)
    (δ : Fin n → ℝ)
    (a : Fin (n - 1)) :
    (section43ScalarDiffCLE n).symm δ
          (Fin.cast (Nat.sub_add_cancel hn) a.succ) -
        (section43ScalarDiffCLE n).symm δ
          (Fin.cast (Nat.sub_add_cancel hn) a.castSucc) =
      δ (Fin.cast (Nat.sub_add_cancel hn) a.succ) := by
  have h := congrFun
    ((section43ScalarDiffCLE n).apply_symm_apply δ)
    (Fin.cast (Nat.sub_add_cancel hn) a.succ)
  simpa [section43ScalarDiffCLE_apply] using h

theorem generatorBlockGlobalTimeAffine_displacement
    {k : ℕ}
    (i : GeneratorIndex k)
    (τ : Fin k → ℝ) :
    osiiAxisPairBlockGlobalTimeAffine
        i.n i.m 0 (τ i.bridgeGlobalIndex)
        (generatorBlockTimeDisplacement i τ) =
      generatorGlobalTimeDisplacement i τ := by
  ext c
  rw [← section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
    i.n i.m i.hn i.hm]
  rw [section43ScalarDiffCLE_apply]
  by_cases hc0 : c.val = 0
  · rw [dif_pos hc0]
    have hc : c = (⟨0, by omega⟩ : Fin (i.n + i.m)) := by
      apply Fin.ext
      exact hc0
    rw [hc]
    have hidx :
        (⟨0, by omega⟩ : Fin (i.n + i.m)) =
          Fin.castAdd i.m (⟨0, i.hn⟩ : Fin i.n) := by
      apply Fin.ext
      rfl
    rw [hidx]
    rw [osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
    have hsum :
        (∑ x : Fin i.n,
            splitFirst i.n i.m
              (generatorBlockTimeDisplacement i τ) x) =
          -(∑ a : Fin (i.n - 1), τ (i.leftGlobalIndex a)) := by
      calc
        _ =
            ∑ x : Fin ((i.n - 1) + 1),
              splitFirst i.n i.m
                (generatorBlockTimeDisplacement i τ)
                (Fin.cast (Nat.sub_add_cancel i.hn) x) := by
              symm
              exact Equiv.sum_comp
                (finCongr (Nat.sub_add_cancel i.hn))
                (fun x : Fin i.n =>
                  splitFirst i.n i.m
                    (generatorBlockTimeDisplacement i τ) x)
        _ = _ := by
          rw [Fin.sum_univ_succ]
          have hzero :
              Fin.cast (Nat.sub_add_cancel i.hn)
                  (0 : Fin ((i.n - 1) + 1)) =
                (⟨0, i.hn⟩ : Fin i.n) := by
            apply Fin.ext
            rfl
          rw [hzero]
          have hqzero :=
            generatorBlockTimeDisplacement_left_zero i τ
          have hqsucc :=
            generatorBlockTimeDisplacement_left_succ i τ
          simp only [splitFirst]
          rw [hqzero]
          simp only [zero_add]
          simp_rw [hqsucc]
          rw [Finset.sum_neg_distrib]
    have hcumulative :
        (section43ScalarDiffCLE i.n).symm
            (splitFirst i.n i.m
              (generatorBlockTimeDisplacement i τ))
            (Fin.rev (⟨0, i.hn⟩ : Fin i.n)) =
          ∑ x : Fin i.n,
            splitFirst i.n i.m
              (generatorBlockTimeDisplacement i τ) x := by
      rw [section43ScalarDiffCLE_symm_apply]
      rw [← Equiv.sum_comp (finCongr (Nat.sub_add_cancel i.hn))]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
    rw [hcumulative, hsum]
    simp [generatorGlobalTimeDisplacement]
  · rw [dif_neg hc0]
    let C : Fin (k + 1) := Fin.cast i.pointArity_add c
    have hC0 : C ≠ 0 := by
      intro hC
      apply hc0
      have := congrArg Fin.val hC
      simpa [C] using this
    obtain ⟨j, hCj⟩ := Fin.eq_succ_of_ne_zero hC0
    have hcval : c.val = j.val + 1 := by
      have := congrArg Fin.val hCj
      simpa [C] using this
    have htarget :
        generatorGlobalTimeDisplacement i τ c =
          if j.val < i.bridgeGlobalIndex.val then -τ j else τ j := by
      simp [generatorGlobalTimeDisplacement, C, hCj]
    rw [htarget]
    by_cases hjleft : j.val < i.bridgeGlobalIndex.val
    · rw [if_pos hjleft]
      have hjgap : j.val < i.toGap.val := by
        simpa [GeneratorIndex.bridgeGlobalIndex_eq_toGap] using hjleft
      have hjn : j.val < i.n - 1 := by
        simpa [GeneratorIndex.bridgeGlobalIndex] using hjleft
      let jL : Fin (i.n - 1) := ⟨j.val, hjn⟩
      let a : Fin (i.n - 1) := Fin.rev jL
      let current : Fin i.n :=
        Fin.cast (Nat.sub_add_cancel i.hn) jL.succ
      let previous : Fin i.n :=
        Fin.cast (Nat.sub_add_cancel i.hn) jL.castSucc
      have hc :
          c = Fin.castAdd i.m current := by
        apply Fin.ext
        simp [current, jL, hcval]
      have hprev :
          (⟨c.val - 1, by omega⟩ : Fin (i.n + i.m)) =
            Fin.castAdd i.m previous := by
        apply Fin.ext
        simp [previous, jL, hcval]
      rw [hprev, hc,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_left,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
      have hrevCurrent :
          Fin.rev current =
            Fin.cast (Nat.sub_add_cancel i.hn) a.castSucc := by
        apply Fin.ext
        simp [current, a, jL]
      have hrevPrevious :
          Fin.rev previous =
            Fin.cast (Nat.sub_add_cancel i.hn) a.succ := by
        apply Fin.ext
        simp [previous, a, jL]
        have hpos : 0 < i.toGap.val - j.val :=
          Nat.sub_pos_of_lt hjgap
        omega
      rw [hrevCurrent, hrevPrevious]
      have hdiff :=
        section43ScalarDiffCLE_symm_cast_succ_sub_cast_castSucc
          i.hn
          (splitFirst i.n i.m
            (generatorBlockTimeDisplacement i τ))
          a
      have hmode :
          i.leftGlobalIndex a = j := by
        apply Fin.ext
        simp [a, jL, GeneratorIndex.leftGlobalIndex]
      have hq :
          splitFirst i.n i.m
              (generatorBlockTimeDisplacement i τ)
              (Fin.cast (Nat.sub_add_cancel i.hn) a.succ) =
            -τ j := by
        rw [show
            splitFirst i.n i.m
                (generatorBlockTimeDisplacement i τ)
                (Fin.cast (Nat.sub_add_cancel i.hn) a.succ) =
              generatorBlockTimeDisplacement i τ
                (Fin.castAdd i.m
                  (Fin.cast (Nat.sub_add_cancel i.hn) a.succ)) by rfl]
        rw [generatorBlockTimeDisplacement_left_succ, hmode]
      rw [← hq]
      linarith
    · rw [if_neg hjleft]
      by_cases hjbridge : j = i.bridgeGlobalIndex
      · subst j
        have hc :
            c =
              Fin.natAdd i.n (⟨0, i.hm⟩ : Fin i.m) := by
          apply Fin.ext
          simp [hcval, GeneratorIndex.bridgeGlobalIndex]
        have hprev :
            (⟨c.val - 1, by omega⟩ : Fin (i.n + i.m)) =
              Fin.castAdd i.m
                (Fin.cast (Nat.sub_add_cancel i.hn)
                  (Fin.last (i.n - 1))) := by
          apply Fin.ext
          simp [hcval, GeneratorIndex.bridgeGlobalIndex]
        rw [hprev, hc,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
        have hrightZero :
            (section43ScalarDiffCLE i.m).symm
                (splitLast i.n i.m
                  (generatorBlockTimeDisplacement i τ))
                (⟨0, i.hm⟩ : Fin i.m) = 0 := by
          rw [section43ScalarDiffCLE_symm_apply]
          simpa [splitLast] using
            generatorBlockTimeDisplacement_right_zero i τ
        have hleftZero :
            (section43ScalarDiffCLE i.n).symm
                (splitFirst i.n i.m
                  (generatorBlockTimeDisplacement i τ))
                (Fin.rev
                  (Fin.cast (Nat.sub_add_cancel i.hn)
                    (Fin.last (i.n - 1)))) = 0 := by
          have hrev :
              Fin.rev
                  (Fin.cast (Nat.sub_add_cancel i.hn)
                    (Fin.last (i.n - 1))) =
                (⟨0, i.hn⟩ : Fin i.n) := by
            apply Fin.ext
            simp
          rw [hrev, section43ScalarDiffCLE_symm_apply]
          simpa [splitFirst] using
            generatorBlockTimeDisplacement_left_zero i τ
        rw [hrightZero, hleftZero]
        ring
      · have hjright : i.bridgeGlobalIndex.val < j.val := by
          have hle : i.bridgeGlobalIndex.val ≤ j.val :=
            le_of_not_gt hjleft
          exact lt_of_le_of_ne hle (by
            intro h
            apply hjbridge
            apply Fin.ext
            exact h.symm)
        have hjn : i.n ≤ j.val := by
          simpa [GeneratorIndex.bridgeGlobalIndex] using
            Nat.succ_le_iff.mpr hjright
        have hsum : k + 1 = i.n + i.m :=
          i.pointArity_add.symm
        have hsum' : i.n + i.m = k + 1 :=
          i.pointArity_add
        have hnm : k = i.n + i.m - 1 := i.hnm
        let b : Fin (i.m - 1) :=
          ⟨j.val - i.n, by
            have hjlt : j.val < k := j.isLt
            omega⟩
        let current : Fin i.m :=
          Fin.cast (Nat.sub_add_cancel i.hm) b.succ
        let previous : Fin i.m :=
          Fin.cast (Nat.sub_add_cancel i.hm) b.castSucc
        have hcurrentVal :
            current.val = j.val - i.n + 1 := by
          simp [current, b]
        have hpreviousVal :
            previous.val = j.val - i.n := by
          simp [previous, b]
        have hc :
            c = Fin.natAdd i.n current := by
          apply Fin.ext
          change c.val = i.n + current.val
          rw [hcval, hcurrentVal]
          omega
        have hprev :
            (⟨c.val - 1, by omega⟩ : Fin (i.n + i.m)) =
              Fin.natAdd i.n previous := by
          apply Fin.ext
          change c.val - 1 = i.n + previous.val
          rw [hcval, hpreviousVal]
          omega
        rw [hprev, hc,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right]
        have hdiff :=
          section43ScalarDiffCLE_symm_cast_succ_sub_cast_castSucc
            i.hm
            (splitLast i.n i.m
              (generatorBlockTimeDisplacement i τ))
            b
        have hmode :
            i.rightGlobalIndex b = j := by
          apply Fin.ext
          change i.n + b.val = j.val
          simpa [b] using Nat.add_sub_of_le hjn
        have hq :
            splitLast i.n i.m
                (generatorBlockTimeDisplacement i τ)
                (Fin.cast (Nat.sub_add_cancel i.hm) b.succ) =
              τ j := by
          rw [show
              splitLast i.n i.m
                  (generatorBlockTimeDisplacement i τ)
                  (Fin.cast (Nat.sub_add_cancel i.hm) b.succ) =
                generatorBlockTimeDisplacement i τ
                  (Fin.natAdd i.n
                    (Fin.cast (Nat.sub_add_cancel i.hm) b.succ)) by rfl]
          rw [generatorBlockTimeDisplacement_right_succ, hmode]
        rw [← hq]
        linarith

/-- In chronological coordinates the split-dependent sign changes disappear:
the tail of the global displacement is exactly the common physical gap
vector. The zeroth coordinate records the reflected-left cumulative shift. -/
theorem generatorGlobalTimeDisplacement_chronologicalParameter
    {k : ℕ}
    (i : GeneratorIndex k)
    (ξ : Fin k → ℝ) :
    generatorGlobalTimeDisplacement i
        (generatorChronologicalParameter i ξ) =
      fun c =>
        generatorPhysicalTimePoint
          (-(∑ a : Fin (i.n - 1), ξ (i.leftGlobalIndex a)))
          ξ (Fin.cast i.pointArity_add c) := by
  funext c
  simp only [generatorGlobalTimeDisplacement,
    generatorPhysicalTimePoint]
  generalize hC :
    Fin.cast i.pointArity_add c = C
  refine Fin.cases ?_ (fun j => ?_) C
  · simp
  · by_cases hj : j < i.toGap
    · simp [generatorChronologicalParameter,
        GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]
    · simp [generatorChronologicalParameter,
        GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]

private theorem osiiAxisPairBlockGlobalTimeAffine_add_commonShift
    (n m : ℕ)
    (s t : ℝ)
    (δ : Fin (n + m) → ℝ) :
    osiiAxisPairBlockGlobalTimeAffine n m s t δ =
      osiiAxisPairBlockGlobalTimeAffine n m 0 t δ +
        fun c => if c.val = 0 then s else 0 := by
  ext c
  simp [osiiAxisPairBlockGlobalTimeAffine,
    osiiAxisPairGlobalTimeDiffShift]
  ring

/-- Canonical split-to-physical time identity. After applying the
split-aware chronological parameter and compensating common translation,
every Chapter V split produces the same full physical difference-time point
`(t₀, ξ)`. -/
theorem generatorBlockGlobalTimeAffine_chronologicalParameter
    {k : ℕ}
    (i : GeneratorIndex k)
    (t₀ : ℝ)
    (ξ : Fin k → ℝ) :
    osiiAxisPairBlockGlobalTimeAffine
        i.n i.m
        (generatorChronologicalCommonShift i t₀ ξ)
        (ξ i.bridgeGlobalIndex)
        (generatorBlockTimeDisplacement i
          (generatorChronologicalParameter i ξ)) =
      fun c =>
        generatorPhysicalTimePoint t₀ ξ
          (Fin.cast i.pointArity_add c) := by
  rw [← generatorChronologicalParameter_bridge i ξ]
  rw [osiiAxisPairBlockGlobalTimeAffine_add_commonShift]
  rw [generatorBlockGlobalTimeAffine_displacement]
  rw [generatorGlobalTimeDisplacement_chronologicalParameter]
  ext c
  simp only [Pi.add_apply]
  by_cases hc0 : c.val = 0
  · have hcast :
        Fin.cast i.pointArity_add c = 0 := by
      apply Fin.ext
      exact hc0
    rw [if_pos hc0, hcast]
    simp [generatorChronologicalCommonShift]
  · have hcast0 :
        Fin.cast i.pointArity_add c ≠ 0 := by
      intro hzero
      apply hc0
      have := congrArg Fin.val hzero
      simpa using this
    obtain ⟨j, hcast⟩ :=
      Fin.eq_succ_of_ne_zero hcast0
    rw [if_neg hc0, hcast]
    simp [generatorPhysicalTimePoint]

/-- Vary only the distinguished head coordinate in each block difference
profile. -/
def axisPairBlockHeadDisplacement
    (n m : ℕ)
    (u v : ℝ) :
    Fin (n + m) → ℝ :=
  Fin.append
    (fun a => if a.val = 0 then u else 0)
    (fun b => if b.val = 0 then v else 0)

@[simp] theorem axisPairBlockHeadDisplacement_left
    (n m : ℕ)
    (u v : ℝ)
    (a : Fin n) :
    axisPairBlockHeadDisplacement n m u v (Fin.castAdd m a) =
      if a.val = 0 then u else 0 := by
  simp [axisPairBlockHeadDisplacement]

@[simp] theorem axisPairBlockHeadDisplacement_right
    (n m : ℕ)
    (u v : ℝ)
    (b : Fin m) :
    axisPairBlockHeadDisplacement n m u v (Fin.natAdd n b) =
      if b.val = 0 then v else 0 := by
  simp [axisPairBlockHeadDisplacement]

/-- The two head coordinates translate their whole absolute-time blocks.
Reflection changes the left translation from `u` to `-u`. -/
theorem osiiAxisPairBlockGlobalAbsoluteTimeConfig_headDisplacement
    (n m : ℕ)
    (u v : ℝ) :
    osiiAxisPairBlockGlobalAbsoluteTimeConfig n m 0 0
        (axisPairBlockHeadDisplacement n m u v) =
      fun c => if c.val < n then -u else v := by
  ext c
  refine Fin.addCases ?_ ?_ c
  · intro a
    rw [osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
    simp [section43ScalarDiffCLE_symm_apply,
      axisPairBlockHeadDisplacement]
  · intro b
    rw [osiiAxisPairBlockGlobalAbsoluteTimeConfig_right]
    simp [section43ScalarDiffCLE_symm_apply,
      axisPairBlockHeadDisplacement]

/-- The block-global linear chart sends the two block heads to the global
basepoint and bridge coordinates: the reflected left head changes the
basepoint by `-u`, while both heads add to the bridge gap. -/
theorem osiiAxisPairBlockGlobalTimeCLE_headDisplacement
    (n m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m)
    (u v : ℝ) :
    osiiAxisPairBlockGlobalTimeCLE n m
        (axisPairBlockHeadDisplacement n m u v) =
      fun c =>
        if c.val = 0 then -u
        else if c.val = n then u + v
        else 0 := by
  ext c
  rw [show
      osiiAxisPairBlockGlobalTimeCLE n m
          (axisPairBlockHeadDisplacement n m u v) c =
        osiiAxisPairBlockGlobalTimeAffine n m 0 0
          (axisPairBlockHeadDisplacement n m u v) c by
      simp [osiiAxisPairBlockGlobalTimeAffine,
        osiiAxisPairGlobalTimeDiffShift]]
  rw [← section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
    n m hn hm]
  rw [osiiAxisPairBlockGlobalAbsoluteTimeConfig_headDisplacement]
  simp only [section43ScalarDiffCLE_apply]
  by_cases hc0 : c.val = 0
  · rw [dif_pos hc0, if_pos hc0]
    simp [hc0, hn]
  · rw [dif_neg hc0, if_neg hc0]
    by_cases hcn : c.val = n
    · rw [if_pos hcn]
      simp [hcn, hn]
      ring
    · rw [if_neg hcn]
      by_cases hleft : c.val < n
      · simp [hleft]
        have hprev : c.val - 1 < n := by omega
        rw [if_pos hprev]
        ring
      · rw [if_neg hleft]
        have hprev : ¬c.val - 1 < n := by omega
        rw [if_neg hprev]
        ring

/-- Adding two block heads to an arbitrary block displacement changes only
the global basepoint and bridge coordinates. -/
theorem osiiAxisPairBlockGlobalTimeAffine_add_headDisplacement
    (n m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m)
    (s t u v : ℝ)
    (δ : Fin (n + m) → ℝ) :
    osiiAxisPairBlockGlobalTimeAffine n m s t
        (δ + axisPairBlockHeadDisplacement n m u v) =
      osiiAxisPairBlockGlobalTimeAffine n m s t δ +
        fun c =>
          if c.val = 0 then -u
          else if c.val = n then u + v
          else 0 := by
  ext c
  simp only [osiiAxisPairBlockGlobalTimeAffine, map_add, Pi.add_apply]
  rw [osiiAxisPairBlockGlobalTimeCLE_headDisplacement n m hn hm u v]
  ring

/-- Add independent block heads to the chronological split. The left head
moves the global basepoint, and the sum of both heads moves the physical
bridge gap. -/
theorem generatorBlockGlobalTimeAffine_chronologicalParameter_add_heads
    {k : ℕ}
    (i : GeneratorIndex k)
    (t₀ : ℝ)
    (ξ : Fin k → ℝ)
    (u v : ℝ) :
    osiiAxisPairBlockGlobalTimeAffine
        i.n i.m
        (generatorChronologicalCommonShift i t₀ ξ)
        (ξ i.bridgeGlobalIndex)
        (generatorBlockTimeDisplacement i
            (generatorChronologicalParameter i ξ) +
          axisPairBlockHeadDisplacement i.n i.m u v) =
      fun c =>
        generatorPhysicalTimePoint
            (t₀ - u)
            (fun j =>
              if j = i.bridgeGlobalIndex
              then ξ j + u + v
              else ξ j)
            (Fin.cast i.pointArity_add c) := by
  rw [osiiAxisPairBlockGlobalTimeAffine_add_headDisplacement
    i.n i.m i.hn i.hm]
  rw [generatorBlockGlobalTimeAffine_chronologicalParameter]
  ext c
  simp only [Pi.add_apply]
  by_cases hc0 : c.val = 0
  · have hcast :
        Fin.cast i.pointArity_add c = 0 := by
      apply Fin.ext
      exact hc0
    rw [hcast]
    simp [generatorPhysicalTimePoint, hc0]
    ring
  · have hcast0 :
        Fin.cast i.pointArity_add c ≠ 0 := by
      intro hzero
      apply hc0
      have := congrArg Fin.val hzero
      simpa using this
    obtain ⟨j, hcast⟩ :=
      Fin.eq_succ_of_ne_zero hcast0
    have hcval : c.val = j.val + 1 := by
      simpa using congrArg Fin.val hcast
    rw [hcast]
    simp only [generatorPhysicalTimePoint_succ]
    by_cases hj : j = i.bridgeGlobalIndex
    · subst j
      have hcn : c.val = i.n := by
        simpa [hcval, GeneratorIndex.bridgeGlobalIndex]
      rw [if_neg hc0, if_pos hcn, if_pos rfl]
      ring
    · have hcn : c.val ≠ i.n := by
        intro hcn
        apply hj
        apply Fin.ext
        simpa [hcval, GeneratorIndex.bridgeGlobalIndex] using hcn
      rw [if_neg hc0, if_neg hcn, if_neg hj]
      ring

end OSIIChapterV
end OSReconstruction
