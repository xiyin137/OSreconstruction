/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialModes
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneSidedTaylorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVPositiveTimeSourceRealEdge

















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d n k : ℕ} [NeZero d]

/-- Multiplication by a temperate cutoff supported away from coincidences
sends every Schwartz test to the OS-I zero-diagonal test space.  Unlike the
older local A0 cutoff API, the multiplier itself need not decay in spatial
directions. -/
theorem osiiA0TemperateCutoff_mul_mem_zeroDiagonal
    (χ : NPointDomain d n → ℂ)
    (_hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.smulLeftCLM ℂ χ φ) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hxχ : x ∈ tsupport χ :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ) (g := χ) (f := φ) hx).2
  exact Set.disjoint_left.mp hχ_disj hxχ hcoin

/-- The zero-diagonal localization map defined by a temperate, possibly
spatially nondecaying cutoff. -/
noncomputable def osiiA0TemperateCutoffZeroCLM
    (χ : NPointDomain d n → ℂ)
    (hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n)) :
    SchwartzNPoint d n →L[ℂ] ZeroDiagonalSchwartz d n :=
  (SchwartzMap.smulLeftCLM ℂ χ).codRestrict
    (zeroDiagonalSubmodule d n)
    (fun φ => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact osiiA0TemperateCutoff_mul_mem_zeroDiagonal χ hχ hχ_disj φ)

@[simp]
theorem osiiA0TemperateCutoffZeroCLM_coe
    (χ : NPointDomain d n → ℂ)
    (hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n) :
    (osiiA0TemperateCutoffZeroCLM χ hχ hχ_disj φ).1 =
      SchwartzMap.smulLeftCLM ℂ χ φ := rfl

/-- A temperate cutoff equal to one on the source support leaves that source
unchanged after zero-diagonal localization. -/
theorem osiiA0TemperateCutoffZeroCLM_apply_eq_of_one_on_tsupport
    (χ : NPointDomain d n → ℂ)
    (hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hχ_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ x = 1) :
    (osiiA0TemperateCutoffZeroCLM χ hχ hχ_disj φ).1 = φ := by
  ext x
  by_cases hx : x ∈ tsupport (φ : NPointDomain d n → ℂ)
  · rw [osiiA0TemperateCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
    simp [smul_eq_mul, hχ_one x hx]
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [osiiA0TemperateCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
    simp [smul_eq_mul, hφx]

/-- The Schwinger functional localized by a temperate cutoff. -/
noncomputable def osiiA0TemperateCutoffSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    (χ : NPointDomain d n → ℂ)
    (hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n)) :
    SchwartzNPoint d n →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
    (osiiA0TemperateCutoffZeroCLM χ hχ hχ_disj)

/-- On a source whose support lies in the cutoff's one-set, the temperate
localized Schwinger functional is the original OS Schwinger value. -/
theorem osiiA0TemperateCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    (χ : NPointDomain d n → ℂ)
    (hχ : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hφ_zero : VanishesToInfiniteOrderOnCoincidence φ)
    (hχ_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ x = 1) :
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ hχ_disj φ =
      OS.S n (ZeroDiagonalSchwartz.ofClassical φ) := by
  change
    OS.S n (osiiA0TemperateCutoffZeroCLM χ hχ hχ_disj φ) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical φ)
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := φ) hφ_zero]
  congr 1
  apply SetCoe.ext
  exact
    osiiA0TemperateCutoffZeroCLM_apply_eq_of_one_on_tsupport
      χ hχ hχ_disj φ hχ_one

/-- The topological support of the standard finite-time cutoff stays inside
its closed one-sided unit collar. -/
theorem tsupport_section43TimePositiveCutoff_subset_thickening_one
    (n : ℕ) :
    tsupport (section43TimePositiveCutoff n) ⊆
      section43TimePositiveThickening n 1 := by
  refine closure_minimal ?_ ?_
  · intro τ hτ
    by_contra hnot
    exact hτ
      (section43TimePositiveCutoff_eq_zero_of_not_mem_thickening_one hnot)
  · simp only [section43TimePositiveThickening, Set.setOf_forall]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_le continuous_const (continuous_apply i)

/-- Time reflection on an `n`-point configuration as a continuous real-linear
map. -/
noncomputable def chapterVTimeReflectionNCLM
    (d n : ℕ) :
    NPointDomain d n →L[ℝ] NPointDomain d n := by
  let L : NPointDomain d n →ₗ[ℝ] NPointDomain d n :=
    { toFun := timeReflectionN d
      map_add' := by
        intro x y
        ext i μ
        by_cases hμ : μ = 0
        · subst μ
          simp [timeReflectionN, timeReflection]
          ring
        · simp [timeReflectionN, timeReflection, hμ]
      map_smul' := by
        intro t x
        ext i μ
        by_cases hμ : μ = 0
        · subst μ
          simp [timeReflectionN, timeReflection]
        · simp [timeReflectionN, timeReflection, hμ] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

@[simp]
theorem chapterVTimeReflectionNCLM_apply
    (d n : ℕ) (x : NPointDomain d n) :
    chapterVTimeReflectionNCLM d n x = timeReflectionN d x :=
  rfl

/-- Positive difference-time coordinates of the reflected left block in a
two-block A0 configuration. -/
noncomputable def reflectedLeftDifferenceTimeCLM
    (d n : ℕ) [NeZero d] :
    NPointDomain d (n + n) →L[ℝ] (Fin n → ℝ) :=
  (section43QTimeCLM d n).comp
    ((section43DiffCoordRealCLE d n).toContinuousLinearMap.comp
      ((chapterVTimeReflectionNCLM d n).comp
        (splitFirstCLM n n)))

@[simp]
theorem reflectedLeftDifferenceTimeCLM_apply
    (d n : ℕ) [NeZero d]
    (x : NPointDomain d (n + n)) :
    reflectedLeftDifferenceTimeCLM d n x =
      section43QTime (d := d) (n := n)
        (section43DiffCoordRealCLE d n
          (timeReflectionN d (splitFirst n n x))) := by
  rfl

/-- Positive difference-time coordinates of the right block in a two-block
A0 configuration. -/
noncomputable def rightDifferenceTimeCLM
    (d n : ℕ) [NeZero d] :
    NPointDomain d (n + n) →L[ℝ] (Fin n → ℝ) :=
  (section43QTimeCLM d n).comp
    ((section43DiffCoordRealCLE d n).toContinuousLinearMap.comp
      (splitLastCLM n n))

@[simp]
theorem rightDifferenceTimeCLM_apply
    (d n : ℕ) [NeZero d]
    (x : NPointDomain d (n + n)) :
    rightDifferenceTimeCLM d n x =
      section43QTime (d := d) (n := n)
        (section43DiffCoordRealCLE d n (splitLast n n x)) := by
  rfl

/-- Affine rescaling used to turn a positive time margin into the standard
smooth one-sided cutoff. -/
def chapterVTimeMarginCutoffArgument
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (scale : ℝ) (L : E →L[ℝ] (Fin n → ℝ)) :
    E → Fin n → ℝ :=
  fun x i => scale * L x i - 2

theorem chapterVTimeMarginCutoffArgument_hasTemperateGrowth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (scale : ℝ) (L : E →L[ℝ] (Fin n → ℝ)) :
    Function.HasTemperateGrowth
      (chapterVTimeMarginCutoffArgument n scale L) := by
  have hscaled :
      Function.HasTemperateGrowth
        (fun x : E => scale • L x) :=
    (Function.HasTemperateGrowth.const scale).smul L.hasTemperateGrowth
  have hconst :
      Function.HasTemperateGrowth
        (fun _ : E => (fun _ : Fin n => (2 : ℝ))) :=
    Function.HasTemperateGrowth.const _
  simpa [chapterVTimeMarginCutoffArgument, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply] using hscaled.sub hconst

/-- A smooth temperate two-block cutoff depending only on the reflected-left
and right difference-time coordinates. -/
noncomputable def osiiA0TwoBlockTimeMarginCutoff
    (d n : ℕ) [NeZero d]
    (ε : ℝ) :
    NPointDomain d (n + n) → ℂ :=
  fun x =>
    section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n) x) *
      section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n) x)

theorem osiiA0TwoBlockTimeMarginCutoff_hasTemperateGrowth
    (d n : ℕ) [NeZero d]
    (ε : ℝ) :
    Function.HasTemperateGrowth
      (osiiA0TwoBlockTimeMarginCutoff d n ε) := by
  have hleft :
      Function.HasTemperateGrowth
        (fun x : NPointDomain d (n + n) =>
          section43TimePositiveCutoff n
            (chapterVTimeMarginCutoffArgument n (2 / ε)
              (reflectedLeftDifferenceTimeCLM d n) x)) :=
    (section43TimePositiveCutoff_hasTemperateGrowth n).comp
      (chapterVTimeMarginCutoffArgument_hasTemperateGrowth n (2 / ε)
        (reflectedLeftDifferenceTimeCLM d n))
  have hright :
      Function.HasTemperateGrowth
        (fun x : NPointDomain d (n + n) =>
          section43TimePositiveCutoff n
            (chapterVTimeMarginCutoffArgument n (2 / ε)
              (rightDifferenceTimeCLM d n) x)) :=
    (section43TimePositiveCutoff_hasTemperateGrowth n).comp
      (chapterVTimeMarginCutoffArgument_hasTemperateGrowth n (2 / ε)
        (rightDifferenceTimeCLM d n))
  simpa [osiiA0TwoBlockTimeMarginCutoff] using hleft.mul hright

/-- The two-block time cutoff is one whenever both blockwise positive
difference-time vectors have the prescribed margin. -/
theorem osiiA0TwoBlockTimeMarginCutoff_eq_one
    (d n : ℕ) [NeZero d]
    {ε : ℝ} (hε : 0 < ε)
    {x : NPointDomain d (n + n)}
    (hleft :
      ∀ i : Fin n, ε ≤ reflectedLeftDifferenceTimeCLM d n x i)
    (hright :
      ∀ i : Fin n, ε ≤ rightDifferenceTimeCLM d n x i) :
    osiiA0TwoBlockTimeMarginCutoff d n ε x = 1 := by
  have hscale : 0 < 2 / ε := div_pos (by norm_num) hε
  have hleft_mem :
      chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n) x ∈
        section43TimePositiveRegion n := by
    intro i
    dsimp [chapterVTimeMarginCutoffArgument]
    have hmul :=
      mul_le_mul_of_nonneg_left (hleft i) hscale.le
    have hεne : ε ≠ 0 := ne_of_gt hε
    have htwo : (2 : ℝ) * ε / ε = 2 := by
      field_simp
    rw [div_mul_eq_mul_div, htwo] at hmul
    linarith
  have hright_mem :
      chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n) x ∈
        section43TimePositiveRegion n := by
    intro i
    dsimp [chapterVTimeMarginCutoffArgument]
    have hmul :=
      mul_le_mul_of_nonneg_left (hright i) hscale.le
    have hεne : ε ≠ 0 := ne_of_gt hε
    have htwo : (2 : ℝ) * ε / ε = 2 := by
      field_simp
    rw [div_mul_eq_mul_div, htwo] at hmul
    linarith
  rw [osiiA0TwoBlockTimeMarginCutoff,
    section43TimePositiveCutoff_eq_one_of_mem hleft_mem,
    section43TimePositiveCutoff_eq_one_of_mem hright_mem, one_mul]

/-- The affine time-cutoff coordinate map is continuous. -/
theorem continuous_chapterVTimeMarginCutoffArgument
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (scale : ℝ) (L : E →L[ℝ] (Fin n → ℝ)) :
    Continuous (chapterVTimeMarginCutoffArgument n scale L) := by
  apply continuous_pi
  intro i
  exact
    ((continuous_const.mul
      ((continuous_apply i).comp L.continuous)).sub continuous_const)

/-- On the topological support of the two-block cutoff, every reflected-left
difference-time coordinate is strictly positive. -/
theorem osiiA0TwoBlockTimeMarginCutoff_tsupport_left_positive
    (d n : ℕ) [NeZero d]
    {ε : ℝ} (hε : 0 < ε)
    {x : NPointDomain d (n + n)}
    (hx : x ∈ tsupport (osiiA0TwoBlockTimeMarginCutoff d n ε)) :
    ∀ i : Fin n, 0 < reflectedLeftDifferenceTimeCLM d n x i := by
  let left : NPointDomain d (n + n) → ℂ :=
    fun y =>
      section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n) y)
  let right : NPointDomain d (n + n) → ℂ :=
    fun y =>
      section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n) y)
  have hxprod : x ∈ tsupport (fun y => left y * right y) := by
    simpa [left, right, osiiA0TwoBlockTimeMarginCutoff] using hx
  have hxleft : x ∈ tsupport left :=
    tsupport_mul_subset_left hxprod
  have harg :
      chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n) x ∈
        tsupport (section43TimePositiveCutoff n) := by
    exact
      tsupport_comp_subset_preimage
        (section43TimePositiveCutoff n)
        (continuous_chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n))
        (by simpa [left, Function.comp_def] using hxleft)
  have hthick :=
    tsupport_section43TimePositiveCutoff_subset_thickening_one n harg
  intro i
  have hi := hthick i
  dsimp [chapterVTimeMarginCutoffArgument] at hi
  have hscale : 0 < 2 / ε := div_pos (by norm_num) hε
  by_contra hnot
  have hnonpos :
      reflectedLeftDifferenceTimeCLM d n x i ≤ 0 :=
    le_of_not_gt hnot
  have hmul :
      (2 / ε) * reflectedLeftDifferenceTimeCLM d n x i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos
  linarith

/-- On the topological support of the two-block cutoff, every right
difference-time coordinate is strictly positive. -/
theorem osiiA0TwoBlockTimeMarginCutoff_tsupport_right_positive
    (d n : ℕ) [NeZero d]
    {ε : ℝ} (hε : 0 < ε)
    {x : NPointDomain d (n + n)}
    (hx : x ∈ tsupport (osiiA0TwoBlockTimeMarginCutoff d n ε)) :
    ∀ i : Fin n, 0 < rightDifferenceTimeCLM d n x i := by
  let left : NPointDomain d (n + n) → ℂ :=
    fun y =>
      section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (reflectedLeftDifferenceTimeCLM d n) y)
  let right : NPointDomain d (n + n) → ℂ :=
    fun y =>
      section43TimePositiveCutoff n
        (chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n) y)
  have hxprod : x ∈ tsupport (fun y => left y * right y) := by
    simpa [left, right, osiiA0TwoBlockTimeMarginCutoff] using hx
  have hxright : x ∈ tsupport right :=
    tsupport_mul_subset_right hxprod
  have harg :
      chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n) x ∈
        tsupport (section43TimePositiveCutoff n) := by
    exact
      tsupport_comp_subset_preimage
        (section43TimePositiveCutoff n)
        (continuous_chapterVTimeMarginCutoffArgument n (2 / ε)
          (rightDifferenceTimeCLM d n))
        (by simpa [right, Function.comp_def] using hxright)
  have hthick :=
    tsupport_section43TimePositiveCutoff_subset_thickening_one n harg
  intro i
  have hi := hthick i
  dsimp [chapterVTimeMarginCutoffArgument] at hi
  have hscale : 0 < 2 / ε := div_pos (by norm_num) hε
  by_contra hnot
  have hnonpos :
      rightDifferenceTimeCLM d n x i ≤ 0 :=
    le_of_not_gt hnot
  have hmul :
      (2 / ε) * rightDifferenceTimeCLM d n x i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos
  linarith

/-- Appending a strictly negative ordered block to a strictly positive
ordered block cannot produce a coincident configuration. -/
theorem finAppend_not_mem_coincidence_of_neg_pos
    {d n m : ℕ}
    (p : NPointDomain d n × NPointDomain d m)
    (hneg : p.1 ∈ OrderedNegativeTimeRegion d n)
    (hpos : p.2 ∈ OrderedPositiveTimeRegion d m) :
    Fin.append p.1 p.2 ∉ CoincidenceLocus d (n + m) := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · let i' : Fin n := ⟨i.1, hi⟩
      let j' : Fin n := ⟨j.1, hj⟩
      have hi_cast : Fin.castAdd m i' = i := by
        ext
        simp [i']
      have hj_cast : Fin.castAdd m j' = j := by
        ext
        simp [j']
      have hij' : i' ≠ j' := by
        intro hij'
        apply hij
        simpa [hi_cast, hj_cast] using
          congrArg (fun t : Fin n => Fin.castAdd m t) hij'
      have hEq : p.1 i' = p.1 j' := by
        rw [← hi_cast, ← hj_cast] at hijEq
        simpa using hijEq
      exact
        (not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion hneg)
          ⟨i', j', hij', hEq⟩
    · let i' : Fin n := ⟨i.1, hi⟩
      let j' : Fin m := ⟨j.1 - n, by omega⟩
      have hi_cast : Fin.castAdd m i' = i := by
        ext
        simp [i']
      have hj_cast : Fin.natAdd n j' = j := by
        ext
        simp [j']
        omega
      have hEq0 : p.1 i' 0 = p.2 j' 0 := by
        have h0 := congrArg (fun y : SpacetimeDim d => y 0) hijEq
        rw [← hi_cast, ← hj_cast] at h0
        simpa using h0
      have hlt : p.1 i' 0 < 0 := (hneg i').1
      have hgt : 0 < p.2 j' 0 := (hpos j').1
      linarith
  · by_cases hj : j.1 < n
    · let i' : Fin m := ⟨i.1 - n, by omega⟩
      let j' : Fin n := ⟨j.1, hj⟩
      have hi_cast : Fin.natAdd n i' = i := by
        ext
        simp [i']
        omega
      have hj_cast : Fin.castAdd m j' = j := by
        ext
        simp [j']
      have hEq0 : p.2 i' 0 = p.1 j' 0 := by
        have h0 := congrArg (fun y : SpacetimeDim d => y 0) hijEq
        rw [← hi_cast, ← hj_cast] at h0
        simpa using h0
      have hgt : 0 < p.2 i' 0 := (hpos i').1
      have hlt : p.1 j' 0 < 0 := (hneg j').1
      linarith
    · let i' : Fin m := ⟨i.1 - n, by omega⟩
      let j' : Fin m := ⟨j.1 - n, by omega⟩
      have hi_cast : Fin.natAdd n i' = i := by
        ext
        simp [i']
        omega
      have hj_cast : Fin.natAdd n j' = j := by
        ext
        simp [j']
        omega
      have hij' : i' ≠ j' := by
        intro hij'
        apply hij
        simpa [hi_cast, hj_cast] using
          congrArg (fun t : Fin m => Fin.natAdd n t) hij'
      have hEq : p.2 i' = p.2 j' := by
        rw [← hi_cast, ← hj_cast] at hijEq
        simpa using hijEq
      exact
        (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion hpos)
          ⟨i', j', hij', hEq⟩

/-- The topological support of the two-block time cutoff is disjoint from the
full coincidence locus. -/
theorem osiiA0TwoBlockTimeMarginCutoff_tsupport_disjoint_coincidence
    (d n : ℕ) [NeZero d]
    {ε : ℝ} (hε : 0 < ε) :
    Disjoint
      (tsupport (osiiA0TwoBlockTimeMarginCutoff d n ε))
      (CoincidenceLocus d (n + n)) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hleft_pos :=
    osiiA0TwoBlockTimeMarginCutoff_tsupport_left_positive
      d n hε hx
  have hright_pos :=
    osiiA0TwoBlockTimeMarginCutoff_tsupport_right_positive
      d n hε hx
  have hleft_delta :
      ∀ i : Fin n,
        0 <
          (section43DiffCoordRealCLE d n
            (timeReflectionN d (splitFirst n n x))) i 0 := by
    intro i
    simpa [reflectedLeftDifferenceTimeCLM_apply,
      section43QTime, nPointTimeSpatialCLE] using hleft_pos i
  have hright_delta :
      ∀ i : Fin n,
        0 < (section43DiffCoordRealCLE d n (splitLast n n x)) i 0 := by
    intro i
    simpa [rightDifferenceTimeCLM_apply,
      section43QTime, nPointTimeSpatialCLE] using hright_pos i
  have hleft_ordered :
      timeReflectionN d (splitFirst n n x) ∈
        OrderedPositiveTimeRegion d n := by
    have h :=
      section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
        d n
        (δ := section43DiffCoordRealCLE d n
          (timeReflectionN d (splitFirst n n x)))
        hleft_delta
    simpa using h
  have hright_ordered :
      splitLast n n x ∈ OrderedPositiveTimeRegion d n := by
    have h :=
      section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
        d n
        (δ := section43DiffCoordRealCLE d n (splitLast n n x))
        hright_delta
    simpa using h
  have hleft_negative :
      splitFirst n n x ∈ OrderedNegativeTimeRegion d n := by
    intro i
    constructor
    · have hi := (hleft_ordered i).1
      simpa [timeReflectionN, timeReflection] using hi
    · intro j hij
      have hij_time := (hleft_ordered i).2 j hij
      simp [timeReflectionN, timeReflection] at hij_time
      linarith
  have happend :
      Fin.append (splitFirst n n x) (splitLast n n x) = x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [splitFirst]
    · intro j
      rw [Fin.append_right]
      rfl
  have hnot :=
    finAppend_not_mem_coincidence_of_neg_pos
      (d := d)
      (splitFirst n n x, splitLast n n x)
      hleft_negative hright_ordered
  rw [happend] at hnot
  exact hnot hcoin

/-- Support of an OS-conjugated tensor product projects through reflection
into the support of its left source. -/
theorem osConjTensorProduct_tsupport_reflectedLeft_mem
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    {x : NPointDomain d (n + m)}
    (hx :
      x ∈ tsupport
        ((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ)) :
    timeReflectionN d (splitFirst n m x) ∈
      tsupport (f : NPointDomain d n → ℂ) := by
  have hxprod :
      x ∈ tsupport
        (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
    simpa [SchwartzNPoint.osConjTensorProduct,
      SchwartzMap.tensorProduct_apply] using hx
  have hxleft_fun :
      x ∈ tsupport
        (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y)) :=
    tsupport_mul_subset_left hxprod
  have hxleft :
      splitFirst n m x ∈
        tsupport ((f.osConj : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) :=
    tsupport_comp_subset_preimage
      ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      (splitFirst_continuousLinear n m) hxleft_fun
  have hxstar :
      splitFirst n m x ∈
        tsupport
          (fun y : NPointDomain d n =>
            f (timeReflectionN d y)) :=
    (tsupport_comp_subset
      (g := starRingEnd ℂ) (map_zero _)
      (fun y : NPointDomain d n => f (timeReflectionN d y))) hxleft
  exact
    tsupport_comp_subset_preimage
      (f : NPointDomain d n → ℂ)
      (chapterVTimeReflectionNCLM d n).continuous hxstar

/-- Support of an OS-conjugated tensor product projects into the support of
its right source. -/
theorem osConjTensorProduct_tsupport_right_mem
    {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    {x : NPointDomain d (n + m)}
    (hx :
      x ∈ tsupport
        ((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ)) :
    splitLast n m x ∈ tsupport (g : NPointDomain d m → ℂ) := by
  have hxprod :
      x ∈ tsupport
        (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
    simpa [SchwartzNPoint.osConjTensorProduct,
      SchwartzMap.tensorProduct_apply] using hx
  have hxright_fun :
      x ∈ tsupport
        (fun y : NPointDomain d (n + m) =>
          g (splitLast n m y)) :=
    tsupport_mul_subset_right hxprod
  exact
    tsupport_comp_subset_preimage
      (g : NPointDomain d m → ℂ)
      (splitLast_continuousLinear n m) hxright_fun

/-- A spacetime source has compact strict-positive difference-time support if
the difference-time projection of its topological support is carried by one
compact subset of the strict-positive orthant.  No spatial compactness is
required. -/
def HasCompactStrictPositiveDifferenceTimeSupport
    (f : SchwartzNPoint d n) : Prop :=
  ∃ K : Set (Fin n → ℝ),
    IsCompact K ∧
      K ⊆ section43TimeStrictPositiveRegion n ∧
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        section43QTime (d := d) (n := n)
            (section43DiffCoordRealCLE d n x) ∈ K

/-- A source family has uniform compact strict-positive difference-time
support if one compact carrier controls the difference-time projection of
every member. The source index may change the spatial Schwartz factor but not
the time carrier. -/
def HasUniformCompactStrictPositiveDifferenceTimeSupport
    {ι : Type*}
    (f : ι → SchwartzNPoint d n) : Prop :=
  ∃ K : Set (Fin n → ℝ),
    IsCompact K ∧
      K ⊆ section43TimeStrictPositiveRegion n ∧
      ∀ a x, x ∈ tsupport (f a : NPointDomain d n → ℂ) →
        section43QTime (d := d) (n := n)
            (section43DiffCoordRealCLE d n x) ∈ K

/-- Compact strict-positive difference-time support gives a uniform positive
margin from every time wall. -/
theorem HasCompactStrictPositiveDifferenceTimeSupport.exists_positive_margin
    {f : SchwartzNPoint d n}
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ δ, 0 < δ ∧
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
        ∀ i : Fin n,
          δ ≤ section43QTime (d := d) (n := n)
            (section43DiffCoordRealCLE d n x) i := by
  classical
  obtain ⟨K, hK_compact, hK_pos, hfK⟩ := hf
  by_cases hnonempty : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hnonempty
    have hcoord_margin :
        ∀ i : Fin n,
          ∃ δ > 0, ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ici δ := by
      intro i
      have himage_compact :
          IsCompact ((fun τ : Fin n → ℝ => τ i) '' K) :=
        hK_compact.image (continuous_apply i)
      have himage_pos :
          ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ioi (0 : ℝ) := by
        rintro _ ⟨τ, hτ, rfl⟩
        exact hK_pos hτ i
      exact
        exists_positive_margin_of_isCompact_subset_Ioi
          himage_compact himage_pos
    choose δ hδ_pos hδ_carrier using hcoord_margin
    let δmin : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
    have hδmin_pos : 0 < δmin := by
      obtain ⟨i, _hi, hmin⟩ :=
        Finset.exists_mem_eq_inf' Finset.univ_nonempty δ
      dsimp [δmin]
      rw [hmin]
      exact hδ_pos i
    refine ⟨δmin, hδmin_pos, ?_⟩
    intro x hx i
    have hδmin_le : δmin ≤ δ i := by
      dsimp [δmin]
      exact Finset.inf'_le δ (Finset.mem_univ i)
    have hcoord :
        section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n x) i ∈
            ((fun τ : Fin n → ℝ => τ i) '' K) :=
      ⟨section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n x), hfK x hx, rfl⟩
    exact hδmin_le.trans (hδ_carrier i hcoord)
  · refine ⟨1, by norm_num, ?_⟩
    intro _x _hx i
    exact False.elim (hnonempty ⟨i⟩)

/-- A common compact strict-positive difference-time carrier gives one
positive margin for every source in the family. -/
theorem HasUniformCompactStrictPositiveDifferenceTimeSupport.exists_positive_margin
    {ι : Type*}
    {f : ι → SchwartzNPoint d n}
    (hf : HasUniformCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ δ, 0 < δ ∧
      ∀ a x, x ∈ tsupport (f a : NPointDomain d n → ℂ) →
        ∀ i : Fin n,
          δ ≤ section43QTime (d := d) (n := n)
            (section43DiffCoordRealCLE d n x) i := by
  classical
  obtain ⟨K, hK_compact, hK_pos, hfK⟩ := hf
  by_cases hnonempty : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hnonempty
    have hcoord_margin :
        ∀ i : Fin n,
          ∃ δ > 0, ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ici δ := by
      intro i
      have himage_compact :
          IsCompact ((fun τ : Fin n → ℝ => τ i) '' K) :=
        hK_compact.image (continuous_apply i)
      have himage_pos :
          ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ioi (0 : ℝ) := by
        rintro _ ⟨τ, hτ, rfl⟩
        exact hK_pos hτ i
      exact
        exists_positive_margin_of_isCompact_subset_Ioi
          himage_compact himage_pos
    choose δ hδ_pos hδ_carrier using hcoord_margin
    let δmin : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
    have hδmin_pos : 0 < δmin := by
      obtain ⟨i, _hi, hmin⟩ :=
        Finset.exists_mem_eq_inf' Finset.univ_nonempty δ
      dsimp [δmin]
      rw [hmin]
      exact hδ_pos i
    refine ⟨δmin, hδmin_pos, ?_⟩
    intro a x hx i
    have hδmin_le : δmin ≤ δ i := by
      dsimp [δmin]
      exact Finset.inf'_le δ (Finset.mem_univ i)
    have hcoord :
        section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n x) i ∈
            ((fun τ : Fin n → ℝ => τ i) '' K) :=
      ⟨section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n x), hfK a x hx, rfl⟩
    exact hδmin_le.trans (hδ_carrier i hcoord)
  · refine ⟨1, by norm_num, ?_⟩
    intro _a _x _hx i
    exact False.elim (hnonempty ⟨i⟩)

/-- A fixed compact strict-positive time profile gives compact
strict-positive difference-time support for every spatial Schwartz factor. -/
theorem section43PositiveTimeSpatialSource_hasCompactStrictPositiveDifferenceTimeSupport
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    HasCompactStrictPositiveDifferenceTimeSupport
      (section43PositiveTimeSpatialSourceCLM d n g χ).1 := by
  refine ⟨tsupport (g.f : (Fin n → ℝ) → ℂ),
    g.compact.isCompact, g.positive, ?_⟩
  intro x hx
  exact
    osiiA0_orderedPullback_tsupport_subset_timeSet
      (d := d) χ g.f
      (tsupport (g.f : (Fin n → ℝ) → ℂ))
      (Subset.refl _)
      (by
        simpa [section43PositiveTimeSpatialSourceCLM_coe] using hx)

/-- Small simultaneous chronological translations preserve a uniform
strict-positive margin in every difference-time coordinate. -/
theorem eventually_chronologicalParameterTranslate_uniform_positive_margin
    {d k : ℕ} [NeZero d]
    (f : SchwartzNPoint d (k + 1))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ ε, 0 < ε ∧
      (∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        ∀ j : Fin (k + 1),
          ε ≤ section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) j) ∧
        ∀ᶠ u : Fin k → ℝ in 𝓝 0,
          ∀ x ∈
            tsupport
              ((translateSchwartzConfiguration
                (sourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                f : SchwartzNPoint d (k + 1)) :
                  NPointDomain d (k + 1) → ℂ),
            ∀ j : Fin (k + 1),
              ε ≤ section43QTime (d := d) (n := k + 1)
                (section43DiffCoordRealCLE d (k + 1) x) j := by
  obtain ⟨δ, hδ_pos, hδ⟩ := hf.exists_positive_margin
  let ε := δ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  refine ⟨ε, hε_pos, ?_, ?_⟩
  · intro x hx j
    have hj := hδ x hx j
    dsimp [ε]
    linarith
  filter_upwards [Metric.ball_mem_nhds (0 : Fin k → ℝ) hε_pos] with u hu
  intro x hx j
  have htranslated :
      x + sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u ∈
        tsupport (f : NPointDomain d (k + 1) → ℂ) := by
    rw [tsupport_translateSchwartzConfiguration_eq_preimage] at hx
    exact hx
  refine Fin.cases ?_ (fun i => ?_) j
  · have hmargin :=
      hδ
        (x + sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u)
        htranslated (0 : Fin (k + 1))
    have hformula :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) u x (0 : Fin (k + 1))
    have hformula' :
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (x + sourceParameterDisplacementCLM
                (fun r : Fin k =>
                  chronologicalTimeSourceDirection (d := d) r) u)) 0 =
          section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) 0 := by
      simpa using hformula
    dsimp [ε]
    linarith
  · have hu_norm : ‖u‖ < ε := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hui_norm : ‖u i‖ < ε :=
      (norm_le_pi_norm u i).trans_lt hu_norm
    have hui_lower : -ε < u i := by
      have hui : |u i| < ε := by
        simpa [Real.norm_eq_abs] using hui_norm
      exact (abs_lt.mp hui).1
    have hmargin :=
      hδ
        (x + sourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u)
        htranslated i.succ
    have hformula :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) u x i.succ
    have hformula' :
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (x + sourceParameterDisplacementCLM
                (fun r : Fin k =>
                  chronologicalTimeSourceDirection (d := d) r) u)) i.succ =
          section43QTime (d := d) (n := k + 1)
              (section43DiffCoordRealCLE d (k + 1) x) i.succ -
            u i := by
      simpa using hformula
    dsimp [ε] at hε_pos hui_lower ⊢
    linarith

/-- Small simultaneous chronological translations preserve one
strict-positive margin uniformly for every member of a source family with a
common compact difference-time carrier. -/
theorem eventually_chronologicalParameterTranslate_family_uniform_positive_margin
    {d k : ℕ} [NeZero d]
    {ι : Type*}
    (f : ι → SchwartzNPoint d (k + 1))
    (hf : HasUniformCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ ε, 0 < ε ∧
      (∀ a x, x ∈ tsupport (f a : NPointDomain d (k + 1) → ℂ) →
        ∀ j : Fin (k + 1),
          ε ≤ section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) j) ∧
        ∀ᶠ u : Fin k → ℝ in 𝓝 0,
          ∀ a x, x ∈
            tsupport
              ((translateSchwartzConfiguration
                (sourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                (f a) : SchwartzNPoint d (k + 1)) :
                  NPointDomain d (k + 1) → ℂ) →
            ∀ j : Fin (k + 1),
              ε ≤ section43QTime (d := d) (n := k + 1)
                (section43DiffCoordRealCLE d (k + 1) x) j := by
  obtain ⟨δ, hδ_pos, hδ⟩ := hf.exists_positive_margin
  let ε := δ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  refine ⟨ε, hε_pos, ?_, ?_⟩
  · intro a x hx j
    have hj := hδ a x hx j
    dsimp [ε]
    linarith
  filter_upwards [Metric.ball_mem_nhds (0 : Fin k → ℝ) hε_pos] with u hu
  intro a x hx j
  have htranslated :
      x + sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u ∈
        tsupport (f a : NPointDomain d (k + 1) → ℂ) := by
    rw [tsupport_translateSchwartzConfiguration_eq_preimage] at hx
    exact hx
  refine Fin.cases ?_ (fun i => ?_) j
  · have hmargin :=
      hδ a
        (x + sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u)
        htranslated (0 : Fin (k + 1))
    have hformula :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) u x (0 : Fin (k + 1))
    have hformula' :
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (x + sourceParameterDisplacementCLM
                (fun r : Fin k =>
                  chronologicalTimeSourceDirection (d := d) r) u)) 0 =
          section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1) x) 0 := by
      simpa using hformula
    dsimp [ε]
    linarith
  · have hu_norm : ‖u‖ < ε := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hui_norm : ‖u i‖ < ε :=
      (norm_le_pi_norm u i).trans_lt hu_norm
    have hui_lower : -ε < u i := by
      have hui : |u i| < ε := by
        simpa [Real.norm_eq_abs] using hui_norm
      exact (abs_lt.mp hui).1
    have hmargin :=
      hδ a
        (x + sourceParameterDisplacementCLM
          (fun r : Fin k =>
            chronologicalTimeSourceDirection (d := d) r) u)
        htranslated i.succ
    have hformula :=
      chronologicalSourceParameterDisplacement_diff_time_apply
        (d := d) u x i.succ
    have hformula' :
        section43QTime (d := d) (n := k + 1)
            (section43DiffCoordRealCLE d (k + 1)
              (x + sourceParameterDisplacementCLM
                (fun r : Fin k =>
                  chronologicalTimeSourceDirection (d := d) r) u)) i.succ =
          section43QTime (d := d) (n := k + 1)
              (section43DiffCoordRealCLE d (k + 1) x) i.succ -
            u i := by
      simpa using hformula
    dsimp [ε] at hε_pos hui_lower ⊢
    linarith

/-- One fixed temperate time-only cutoff is identically one on every
sufficiently small reflected two-block translate of a compact-time source. -/
theorem exists_twoBlockTimeMarginCutoff_one_on_reflectedTranslation_germ
    {d k : ℕ} [NeZero d]
    (f : SchwartzNPoint d (k + 1))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ ε, 0 < ε ∧
      Function.HasTemperateGrowth
        (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε) ∧
      Disjoint
        (tsupport (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε))
        (CoincidenceLocus d ((k + 1) + (k + 1))) ∧
      (∀ x ∈
          tsupport
            ((f.osConjTensorProduct f :
              SchwartzNPoint d ((k + 1) + (k + 1))) :
                NPointDomain d ((k + 1) + (k + 1)) → ℂ),
          osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1) ∧
        ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
          ∀ x ∈
            tsupport
              ((translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                (f.osConjTensorProduct f) :
                  SchwartzNPoint d ((k + 1) + (k + 1))) :
                    NPointDomain d ((k + 1) + (k + 1)) → ℂ),
            osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1 := by
  obtain ⟨ε, hε, hbase, hstable⟩ :=
    eventually_chronologicalParameterTranslate_uniform_positive_margin f hf
  let leftParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.castAdd k i)
  let rightParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.natAdd k i)
  have hleft_cont : Continuous leftParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hright_cont : Continuous rightParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hleft_zero :
      leftParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hright_zero :
      rightParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hleft_tendsto :
      Tendsto leftParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto leftParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (leftParam (0 : Fin (k + k) → ℝ))) :=
      hleft_cont.continuousAt
    rw [hleft_zero] at h
    exact h
  have hright_tendsto :
      Tendsto rightParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto rightParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (rightParam (0 : Fin (k + k) → ℝ))) :=
      hright_cont.continuousAt
    rw [hright_zero] at h
    exact h
  have hleft_stable := hleft_tendsto.eventually hstable
  have hright_stable := hright_tendsto.eventually hstable
  refine ⟨ε, hε,
    osiiA0TwoBlockTimeMarginCutoff_hasTemperateGrowth d (k + 1) ε,
    osiiA0TwoBlockTimeMarginCutoff_tsupport_disjoint_coincidence
      d (k + 1) hε, ?_, ?_⟩
  · intro x hx
    have hxleft :
        timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
          tsupport (f : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_reflectedLeft_mem f f hx
    have hxright :
        splitLast (k + 1) (k + 1) x ∈
          tsupport (f : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_right_mem f f hx
    apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
    · intro j
      simpa [reflectedLeftDifferenceTimeCLM_apply] using
        hbase (timeReflectionN d (splitFirst (k + 1) (k + 1) x))
          hxleft j
    · intro j
      simpa [rightDifferenceTimeCLM_apply] using
        hbase (splitLast (k + 1) (k + 1) x) hxright j
  filter_upwards [hleft_stable, hright_stable] with u hlu hru
  intro x hx
  let a : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (leftParam u)
  let b : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (rightParam u)
  have hdisp :
      Fin.append (timeReflectionN d a) b =
        reflectedSourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u := by
    rfl
  have htranslate :
      (translateSchwartzConfiguration a f).osConjTensorProduct
          (translateSchwartzConfiguration b f) =
        translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          (f.osConjTensorProduct f) := by
    rw [osConjTensorProduct_translateSchwartzConfiguration, hdisp]
  have hxprod :
      x ∈ tsupport
        (((translateSchwartzConfiguration a f).osConjTensorProduct
          (translateSchwartzConfiguration b f) :
            SchwartzNPoint d ((k + 1) + (k + 1))) :
              NPointDomain d ((k + 1) + (k + 1)) → ℂ) := by
    rw [htranslate]
    exact hx
  have hxleft :
      timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
        tsupport
          ((translateSchwartzConfiguration a f :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_reflectedLeft_mem
      (translateSchwartzConfiguration a f)
      (translateSchwartzConfiguration b f) hxprod
  have hxright :
      splitLast (k + 1) (k + 1) x ∈
        tsupport
          ((translateSchwartzConfiguration b f :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_right_mem
      (translateSchwartzConfiguration a f)
      (translateSchwartzConfiguration b f) hxprod
  apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
  · intro j
    simpa [a, leftParam, reflectedLeftDifferenceTimeCLM_apply] using
      hlu (timeReflectionN d (splitFirst (k + 1) (k + 1) x)) hxleft j
  · intro j
    simpa [b, rightParam, rightDifferenceTimeCLM_apply] using
      hru (splitLast (k + 1) (k + 1) x) hxright j

/-- One time-only cutoff and one reflected-translation neighborhood work for
every source in a family sharing a compact strict-positive difference-time
carrier. -/
theorem exists_twoBlockTimeMarginCutoff_one_on_reflectedTranslation_family_germ
    {d k : ℕ} [NeZero d]
    {ι : Type*}
    (f : ι → SchwartzNPoint d (k + 1))
    (hf : HasUniformCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ ε, 0 < ε ∧
      Function.HasTemperateGrowth
        (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε) ∧
      Disjoint
        (tsupport (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε))
        (CoincidenceLocus d ((k + 1) + (k + 1))) ∧
      (∀ a x, x ∈
          tsupport
            (((f a).osConjTensorProduct (f a) :
              SchwartzNPoint d ((k + 1) + (k + 1))) :
                NPointDomain d ((k + 1) + (k + 1)) → ℂ) →
          osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1) ∧
        ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
          ∀ a x, x ∈
            tsupport
              ((translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                ((f a).osConjTensorProduct (f a)) :
                  SchwartzNPoint d ((k + 1) + (k + 1))) :
                    NPointDomain d ((k + 1) + (k + 1)) → ℂ) →
            osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1 := by
  obtain ⟨ε, hε, hbase, hstable⟩ :=
    eventually_chronologicalParameterTranslate_family_uniform_positive_margin
      f hf
  let leftParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.castAdd k i)
  let rightParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.natAdd k i)
  have hleft_cont : Continuous leftParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hright_cont : Continuous rightParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hleft_zero :
      leftParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hright_zero :
      rightParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hleft_tendsto :
      Tendsto leftParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto leftParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (leftParam (0 : Fin (k + k) → ℝ))) :=
      hleft_cont.continuousAt
    rw [hleft_zero] at h
    exact h
  have hright_tendsto :
      Tendsto rightParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto rightParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (rightParam (0 : Fin (k + k) → ℝ))) :=
      hright_cont.continuousAt
    rw [hright_zero] at h
    exact h
  have hleft_stable := hleft_tendsto.eventually hstable
  have hright_stable := hright_tendsto.eventually hstable
  refine ⟨ε, hε,
    osiiA0TwoBlockTimeMarginCutoff_hasTemperateGrowth d (k + 1) ε,
    osiiA0TwoBlockTimeMarginCutoff_tsupport_disjoint_coincidence
      d (k + 1) hε, ?_, ?_⟩
  · intro a x hx
    have hxleft :
        timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
          tsupport (f a : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_reflectedLeft_mem (f a) (f a) hx
    have hxright :
        splitLast (k + 1) (k + 1) x ∈
          tsupport (f a : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_right_mem (f a) (f a) hx
    apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
    · intro j
      simpa [reflectedLeftDifferenceTimeCLM_apply] using
        hbase a (timeReflectionN d (splitFirst (k + 1) (k + 1) x))
          hxleft j
    · intro j
      simpa [rightDifferenceTimeCLM_apply] using
        hbase a (splitLast (k + 1) (k + 1) x) hxright j
  filter_upwards [hleft_stable, hright_stable] with u hlu hru
  intro a x hx
  let leftTranslation : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (leftParam u)
  let rightTranslation : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (rightParam u)
  have hdisp :
      Fin.append (timeReflectionN d leftTranslation) rightTranslation =
        reflectedSourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u := by
    rfl
  have htranslate :
      (translateSchwartzConfiguration leftTranslation (f a)).osConjTensorProduct
          (translateSchwartzConfiguration rightTranslation (f a)) =
        translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          ((f a).osConjTensorProduct (f a)) := by
    rw [osConjTensorProduct_translateSchwartzConfiguration, hdisp]
  have hxprod :
      x ∈ tsupport
        (((translateSchwartzConfiguration
              leftTranslation (f a)).osConjTensorProduct
          (translateSchwartzConfiguration rightTranslation (f a)) :
            SchwartzNPoint d ((k + 1) + (k + 1))) :
              NPointDomain d ((k + 1) + (k + 1)) → ℂ) := by
    rw [htranslate]
    exact hx
  have hxleft :
      timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
        tsupport
          ((translateSchwartzConfiguration leftTranslation (f a) :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_reflectedLeft_mem
      (translateSchwartzConfiguration leftTranslation (f a))
      (translateSchwartzConfiguration rightTranslation (f a)) hxprod
  have hxright :
      splitLast (k + 1) (k + 1) x ∈
        tsupport
          ((translateSchwartzConfiguration rightTranslation (f a) :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_right_mem
      (translateSchwartzConfiguration leftTranslation (f a))
      (translateSchwartzConfiguration rightTranslation (f a)) hxprod
  apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
  · intro j
    simpa [leftTranslation, leftParam,
      reflectedLeftDifferenceTimeCLM_apply] using
      hlu a (timeReflectionN d (splitFirst (k + 1) (k + 1) x))
        hxleft j
  · intro j
    simpa [rightTranslation, rightParam,
      rightDifferenceTimeCLM_apply] using
      hru a (splitLast (k + 1) (k + 1) x) hxright j

/-- One time-only cutoff and one reflected-translation neighborhood work for
every mixed pair of sources in a family sharing a compact strict-positive
difference-time carrier. -/
theorem
    exists_twoBlockTimeMarginCutoff_one_on_mixedReflectedTranslation_family_germ
    {d k : ℕ} [NeZero d]
    {ι : Type*}
    (f : ι → SchwartzNPoint d (k + 1))
    (hf : HasUniformCompactStrictPositiveDifferenceTimeSupport f) :
    ∃ ε, 0 < ε ∧
      Function.HasTemperateGrowth
        (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε) ∧
      Disjoint
        (tsupport (osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε))
        (CoincidenceLocus d ((k + 1) + (k + 1))) ∧
      (∀ a b x, x ∈
          tsupport
            (((f a).osConjTensorProduct (f b) :
              SchwartzNPoint d ((k + 1) + (k + 1))) :
                NPointDomain d ((k + 1) + (k + 1)) → ℂ) →
          osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1) ∧
        ∀ᶠ u : Fin (k + k) → ℝ in 𝓝 0,
          ∀ a b x, x ∈
            tsupport
              ((translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                ((f a).osConjTensorProduct (f b)) :
                  SchwartzNPoint d ((k + 1) + (k + 1))) :
                    NPointDomain d ((k + 1) + (k + 1)) → ℂ) →
            osiiA0TwoBlockTimeMarginCutoff d (k + 1) ε x = 1 := by
  obtain ⟨ε, hε, hbase, hstable⟩ :=
    eventually_chronologicalParameterTranslate_family_uniform_positive_margin
      f hf
  let leftParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.castAdd k i)
  let rightParam : (Fin (k + k) → ℝ) → (Fin k → ℝ) :=
    fun u i => u (Fin.natAdd k i)
  have hleft_cont : Continuous leftParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hright_cont : Continuous rightParam := by
    apply continuous_pi
    intro i
    exact continuous_apply _
  have hleft_zero :
      leftParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hright_zero :
      rightParam (0 : Fin (k + k) → ℝ) = (0 : Fin k → ℝ) := rfl
  have hleft_tendsto :
      Tendsto leftParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto leftParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (leftParam (0 : Fin (k + k) → ℝ))) :=
      hleft_cont.continuousAt
    rw [hleft_zero] at h
    exact h
  have hright_tendsto :
      Tendsto rightParam
        (𝓝 (0 : Fin (k + k) → ℝ)) (𝓝 (0 : Fin k → ℝ)) := by
    have h :
        Tendsto rightParam
          (𝓝 (0 : Fin (k + k) → ℝ))
          (𝓝 (rightParam (0 : Fin (k + k) → ℝ))) :=
      hright_cont.continuousAt
    rw [hright_zero] at h
    exact h
  have hleft_stable := hleft_tendsto.eventually hstable
  have hright_stable := hright_tendsto.eventually hstable
  refine ⟨ε, hε,
    osiiA0TwoBlockTimeMarginCutoff_hasTemperateGrowth d (k + 1) ε,
    osiiA0TwoBlockTimeMarginCutoff_tsupport_disjoint_coincidence
      d (k + 1) hε, ?_, ?_⟩
  · intro a b x hx
    have hxleft :
        timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
          tsupport (f a : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_reflectedLeft_mem (f a) (f b) hx
    have hxright :
        splitLast (k + 1) (k + 1) x ∈
          tsupport (f b : NPointDomain d (k + 1) → ℂ) :=
      osConjTensorProduct_tsupport_right_mem (f a) (f b) hx
    apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
    · intro j
      simpa [reflectedLeftDifferenceTimeCLM_apply] using
        hbase a (timeReflectionN d (splitFirst (k + 1) (k + 1) x))
          hxleft j
    · intro j
      simpa [rightDifferenceTimeCLM_apply] using
        hbase b (splitLast (k + 1) (k + 1) x) hxright j
  filter_upwards [hleft_stable, hright_stable] with u hlu hru
  intro a b x hx
  let leftTranslation : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (leftParam u)
  let rightTranslation : NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k => chronologicalTimeSourceDirection (d := d) i)
      (rightParam u)
  have hdisp :
      Fin.append (timeReflectionN d leftTranslation) rightTranslation =
        reflectedSourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u := by
    rfl
  have htranslate :
      (translateSchwartzConfiguration leftTranslation (f a)).osConjTensorProduct
          (translateSchwartzConfiguration rightTranslation (f b)) =
        translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          ((f a).osConjTensorProduct (f b)) := by
    rw [osConjTensorProduct_translateSchwartzConfiguration, hdisp]
  have hxprod :
      x ∈ tsupport
        (((translateSchwartzConfiguration
              leftTranslation (f a)).osConjTensorProduct
          (translateSchwartzConfiguration rightTranslation (f b)) :
            SchwartzNPoint d ((k + 1) + (k + 1))) :
              NPointDomain d ((k + 1) + (k + 1)) → ℂ) := by
    rw [htranslate]
    exact hx
  have hxleft :
      timeReflectionN d (splitFirst (k + 1) (k + 1) x) ∈
        tsupport
          ((translateSchwartzConfiguration leftTranslation (f a) :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_reflectedLeft_mem
      (translateSchwartzConfiguration leftTranslation (f a))
      (translateSchwartzConfiguration rightTranslation (f b)) hxprod
  have hxright :
      splitLast (k + 1) (k + 1) x ∈
        tsupport
          ((translateSchwartzConfiguration rightTranslation (f b) :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) :=
    osConjTensorProduct_tsupport_right_mem
      (translateSchwartzConfiguration leftTranslation (f a))
      (translateSchwartzConfiguration rightTranslation (f b)) hxprod
  apply osiiA0TwoBlockTimeMarginCutoff_eq_one d (k + 1) hε
  · intro j
    simpa [leftTranslation, leftParam,
      reflectedLeftDifferenceTimeCLM_apply] using
      hlu a (timeReflectionN d (splitFirst (k + 1) (k + 1) x))
        hxleft j
  · intro j
    simpa [rightTranslation, rightParam,
      rightDifferenceTimeCLM_apply] using
      hru b (splitLast (k + 1) (k + 1) x) hxright j

/-- A temperate cutoff which is one on a reflected product support computes
every normalized reflected source coefficient. -/
theorem osiiA0TemperateCutoffSchwingerCLM_normalized_reflectedProduct_eq
    {d n r : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (directions : Fin r → NPointDomain d n)
    (α β : Fin r → ℕ)
    (f g : SchwartzNPoint d n)
    (χ : NPointDomain d (n + n) → ℂ)
    (hχ_growth : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d (n + n)))
    (hχ_one :
      ∀ x ∈ tsupport
        (((f.osConjTensorProduct g : SchwartzNPoint d (n + n)) :
          NPointDomain d (n + n) → ℂ)),
        χ x = 1)
    (hfg_disj :
      Disjoint
        (tsupport
          (((f.osConjTensorProduct g : SchwartzNPoint d (n + n)) :
            NPointDomain d (n + n) → ℂ)))
        (CoincidenceLocus d (n + n))) :
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
        (SchwartzNPoint.osConjTensorProduct
          (normalizedSourceMultiDerivative directions α f :
            SchwartzNPoint d n)
          (normalizedSourceMultiDerivative directions β g :
            SchwartzNPoint d n)) =
      OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical
          (SchwartzNPoint.osConjTensorProduct
            (normalizedSourceMultiDerivative directions α f :
              SchwartzNPoint d n)
            (normalizedSourceMultiDerivative directions β g :
              SchwartzNPoint d n))) := by
  let φ : SchwartzNPoint d (n + n) := f.osConjTensorProduct g
  let ψ : SchwartzNPoint d (n + n) :=
    normalizedSourceMultiDerivative
      (reflectedProductSourceDirections directions)
      (Fin.append α β) φ
  have hψ_sub :
      tsupport (ψ : NPointDomain d (n + n) → ℂ) ⊆
        tsupport (φ : NPointDomain d (n + n) → ℂ) :=
    tsupport_normalizedSourceMultiDerivative_subset
      (reflectedProductSourceDirections directions) (Fin.append α β) φ
  have hψ_disj :
      Disjoint
        (tsupport (ψ : NPointDomain d (n + n) → ℂ))
        (CoincidenceLocus d (n + n)) :=
    hfg_disj.mono_left hψ_sub
  have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      (f := ψ) hψ_disj
  calc
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
        (SchwartzNPoint.osConjTensorProduct
          (normalizedSourceMultiDerivative directions α f :
            SchwartzNPoint d n)
          (normalizedSourceMultiDerivative directions β g :
            SchwartzNPoint d n)) =
      osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj ψ := by
        change
          osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
              (SchwartzNPoint.osConjTensorProduct
                (normalizedSourceMultiDerivative directions α f :
                  SchwartzNPoint d n)
                (normalizedSourceMultiDerivative directions β g :
                  SchwartzNPoint d n)) =
            osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
              (normalizedSourceMultiDerivative
                (reflectedProductSourceDirections directions)
                (Fin.append α β) (f.osConjTensorProduct g))
        rw [normalizedSourceMultiDerivative_reflectedProduct_append]
    _ = OS.S (n + n) (ZeroDiagonalSchwartz.ofClassical ψ) := by
      exact
        osiiA0TemperateCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
          OS χ hχ_growth hχ_disj ψ hψ_zero
          (fun x hx => hχ_one x (hψ_sub hx))
    _ = OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical
          (SchwartzNPoint.osConjTensorProduct
            (normalizedSourceMultiDerivative directions α f :
              SchwartzNPoint d n)
            (normalizedSourceMultiDerivative directions β g :
              SchwartzNPoint d n))) := by
      change
        OS.S (n + n)
            (ZeroDiagonalSchwartz.ofClassical
              (normalizedSourceMultiDerivative
                (reflectedProductSourceDirections directions)
                (Fin.append α β) (f.osConjTensorProduct g))) =
          _
      rw [normalizedSourceMultiDerivative_reflectedProduct_append]

/-- A temperate cutoff which is one on a reflected product support computes
every right-source homogeneous Taylor polynomial with that fixed left
source. -/
theorem osiiA0TemperateCutoffSchwingerCLM_homogeneousSource_eq
    {d n r : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (directions : Fin r → NPointDomain d n)
    (g f : euclideanPositiveTimeSubmodule (d := d) n)
    (χ : NPointDomain d (n + n) → ℂ)
    (hχ_growth : Function.HasTemperateGrowth χ)
    (hχ_disj :
      Disjoint (tsupport χ) (CoincidenceLocus d (n + n)))
    (hχ_one :
      ∀ x ∈ tsupport
        (((g.1.osConjTensorProduct f.1 : SchwartzNPoint d (n + n)) :
          NPointDomain d (n + n) → ℂ)),
        χ x = 1)
    (hgf_disj :
      Disjoint
        (tsupport
          (((g.1.osConjTensorProduct f.1 : SchwartzNPoint d (n + n)) :
            NPointDomain d (n + n) → ℂ)))
        (CoincidenceLocus d (n + n)))
    (z : Fin r → ℂ)
    (p : ℕ) :
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
        (g.1.osConjTensorProduct
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            f directions).homogeneousSource z p).1) =
      OS.S (n + n)
        (ZeroDiagonalSchwartz.ofClassical
          (g.1.osConjTensorProduct
            ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
              f directions).homogeneousSource z p).1)) := by
  rw [← osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  let F := PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives f directions
  let Tg : SchwartzNPoint d n →L[ℂ] ℂ :=
    (osiiA0TemperateCutoffSchwingerCLM
      OS χ hχ_growth hχ_disj).comp
      (osConjTensorProductRightCLM g.1)
  change
    Tg (F.homogeneousSource z p).1 =
      @inner ℂ (OSHilbertSpace OS) _
        (osiiPositiveTimeSingleVectorCLM OS n g)
        (osiiPositiveTimeSingleVectorCLM OS n (F.homogeneousSource z p))
  simp only [F, PositiveTimeSourceTaylorFamily.homogeneousSource,
    PositiveTimeSourceTaylorFamily.monomial,
    PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives,
    Submodule.coe_sum, Submodule.coe_smul,
    map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  simpa using
    osiiA0TemperateCutoffSchwingerCLM_normalized_reflectedProduct_eq
      OS directions (0 : Fin r → ℕ) α g.1 f.1 χ
      hχ_growth hχ_disj hχ_one hgf_disj

/-- A genuine scalar real edge supplies the Chapter V source/Cauchy
compatibility for compact-time, arbitrary-spatial chronological sources. -/
theorem reflectedSourceCauchyCompatibility_of_realEdge_compactTime
    {d q : ℕ} [NeZero d]
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f.1)
    (increment : Fin (q + 1) → ℂ)
    (D : ReflectedCauchyCoefficientData (q + 1))
    (hleft :
      ∀ i, D.increment (Fin.castAdd (q + 1) i) =
        starRingEnd ℂ (increment i))
    (hright :
      ∀ i, D.increment (Fin.natAdd (q + 1) i) = increment i)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc D.center (fun _ => D.radius) ⊆ U)
    (hscalar : DifferentiableOn ℂ D.scalar U)
    (hreal :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) i) x)
                (f.1.osConjTensorProduct f.1))))) :
    ReflectedSourceCauchyCompatibility OS
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives f
        (fun i : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) i)
        increment)
      D := by
  let directions : Fin (q + 1) → NPointDomain d (q + 2) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  let φ : SchwartzNPoint d ((q + 2) + (q + 2)) :=
    f.1.osConjTensorProduct f.1
  obtain ⟨ε, hε, hχ_growth, hχ_disj, hχ_base, hχ_local⟩ :=
    exists_twoBlockTimeMarginCutoff_one_on_reflectedTranslation_germ f.1 hf
  let χ : NPointDomain d ((q + 2) + (q + 2)) → ℂ :=
    osiiA0TwoBlockTimeMarginCutoff d (q + 2) ε
  let T : SchwartzNPoint d ((q + 2) + (q + 2)) →L[ℂ] ℂ :=
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
  have hφ_disj :
      Disjoint
        (tsupport
          ((φ : SchwartzNPoint d ((q + 2) + (q + 2))) :
            NPointDomain d ((q + 2) + (q + 2)) → ℂ))
        (CoincidenceLocus d ((q + 2) + (q + 2))) := by
    simpa [φ] using
      osiiA0_osConjTensorProduct_tsupport_disjoint_coincidence_of_ordered
        f.1 f.1 f.2 f.2
  have hlocalT :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        T (translateSchwartzConfiguration
          (reflectedSourceParameterDisplacementCLM directions x) φ)) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM directions x)
                φ))) := by
    filter_upwards [hχ_local] with u hu
    let ψ : SchwartzNPoint d ((q + 2) + (q + 2)) :=
      translateSchwartzConfiguration
        (reflectedSourceParameterDisplacementCLM directions u) φ
    have hψ_disj :
        Disjoint
          (tsupport
            ((ψ : SchwartzNPoint d ((q + 2) + (q + 2))) :
              NPointDomain d ((q + 2) + (q + 2)) → ℂ))
          (CoincidenceLocus d ((q + 2) + (q + 2))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hcoin
      have hχx : χ x = 1 :=
        hu x (by simpa [ψ, φ, directions, χ] using hx)
      have hx_support : x ∈ Function.support χ := by
        intro hxzero
        rw [hxzero] at hχx
        norm_num at hχx
      exact Set.disjoint_left.mp hχ_disj (subset_closure hx_support) hcoin
    have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
      VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
        (f := ψ) hψ_disj
    simpa [T, ψ] using
      osiiA0TemperateCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        OS χ hχ_growth hχ_disj ψ hψ_zero
        (fun x hx => hu x (by simpa [ψ, φ, directions, χ] using hx))
  have hrealT :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions x) φ)) := by
    simpa [directions, φ] using hreal.trans hlocalT.symm
  refine
    { left_increment := hleft
      right_increment := hright
      cauchyCoeff_eq_scalarGram := ?_ }
  intro α β
  calc
    SCV.cauchyCoeffPolydisc D.scalar D.center
        (fun _ => D.radius) (@Fin.append (q + 1) (q + 1) ℕ α β) =
      T (SchwartzNPoint.osConjTensorProduct
        (normalizedSourceMultiDerivative directions α f.1 :
          SchwartzNPoint d (q + 2))
        (normalizedSourceMultiDerivative directions β f.1 :
          SchwartzNPoint d (q + 2))) := by
      exact
        cauchyCoeffPolydisc_eq_localReflectedProduct_normalized
          hTowerC hTowerPi T directions f.1 f.1 D.radius_pos
          hU hRU hscalar (by simpa [φ] using hrealT) α β
    _ =
      (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
        f directions increment).scalarGram OS α β := by
      simpa [PositiveTimeSourceCoefficientData.scalarGram, T, χ] using
        osiiA0TemperateCutoffSchwingerCLM_normalized_reflectedProduct_eq
          OS directions α β f.1 f.1 χ hχ_growth hχ_disj hχ_base hφ_disj

namespace PositiveTimeSourceTaylorFamily

/-- A genuine reflected scalar real edge constructs the locally uniform
holomorphic chronological Hilbert Taylor field for a compact-time,
arbitrary-spatial source. -/
theorem exists_holomorphicField_of_realEdge_compactTime
    {d q : ℕ} [NeZero d]
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (hTowerPi :
      IsScalarTower ℝ ℂ (Fin ((q + 1) + (q + 1)) → ℂ))
    (OS : OsterwalderSchraderAxioms d)
    (f : euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f.1)
    (D : ReflectedCauchyPolydiscData (q + 1))
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU : SCV.closedPolydisc D.center (fun _ => D.radius) ⊆ U)
    (hscalar : DifferentiableOn ℂ D.scalar U)
    (hreal :
      (fun x : Fin ((q + 1) + (q + 1)) → ℝ =>
        realAffineSlice D.scalar D.center x) =ᶠ[𝓝 0]
        (fun x =>
          OS.S ((q + 2) + (q + 2))
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (reflectedSourceParameterDisplacementCLM
                  (fun i : Fin (q + 1) =>
                    chronologicalTimeSourceDirection (d := d) i) x)
                (f.1.osConjTensorProduct f.1))))) :
    ∃ Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS,
      TendstoLocallyUniformlyOn
          ((ofNormalizedDerivatives f
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i)).partialSum OS)
          Ψ atTop
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ) (fun _ => D.radius)) ∧
        DifferentiableOn ℂ Ψ
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ) (fun _ => D.radius)) := by
  let directions : Fin (q + 1) → NPointDomain d (q + 2) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  apply
    (ofNormalizedDerivatives f directions).exists_holomorphicField_of_reflectedPolydisc
      OS D
  intro increment hincrement p r hincrement_reflected
  let E :=
    D.atIncrement
      (reflectedCauchyIncrement increment) hincrement_reflected
  let S :=
    PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
      f directions increment
  have C : ReflectedSourceCauchyCompatibility OS S E := by
    apply
      reflectedSourceCauchyCompatibility_of_realEdge_compactTime
        hTowerC hTowerPi OS f hf increment E
    · intro i
      exact reflectedCauchyIncrement_left increment i
    · intro i
      exact reflectedCauchyIncrement_right increment i
    · exact hU
    · exact hRU
    · exact hscalar
    · exact hreal
  change
    positiveTimeTaylorScalarGram OS (q + 2) S.homogeneousSource p r =
      E.scalarGram p r
  exact
    S.positiveTimeTaylorScalarGram_homogeneousSource_eq_cauchyScalarGram
      OS E C p r

end PositiveTimeSourceTaylorFamily

/-- Pointwise norm-square identification once the reflected scalar Cauchy
series is known to sum at the chosen increment. This is the algebraic core of
the norm-edge proof, separated from any neighborhood or radius selection. -/
theorem norm_sq_holomorphicField_eq_reflectedScalar_of_compatibility_of_hasSum
    {d n q : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin (q + 1) → NPointDomain d n)
    (D : ReflectedCauchyPolydiscData (q + 1))
    (hcompat :
      ∀ (z : Fin (q + 1) → ℂ)
        (hincrement :
          ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius),
        ReflectedSourceCauchyCompatibility OS
          (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
            f directions z)
          (D.atIncrement (reflectedCauchyIncrement z) hincrement))
    (Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          f directions).partialSum OS)
        Ψ atTop
        (SCV.Polydisc
          (0 : Fin (q + 1) → ℂ) (fun _ => D.radius)))
    (z : Fin (q + 1) → ℂ)
    (hzP :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => D.radius))
    (hxsum :
      HasSum
        (fun p =>
          SCV.cauchyPowerSeriesPolydisc D.scalar D.center
            (fun _ => D.radius) p
              (fun _ => reflectedCauchyIncrement z))
        (D.scalar (D.center + reflectedCauchyIncrement z))) :
    ‖Ψ z‖ ^ 2 =
      (D.scalar (D.center + reflectedCauchyIncrement z)).re := by
  let T :=
    PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives f directions
  have hzlt : ∀ i, ‖z i‖ < D.radius := by
    intro i
    simpa [dist_zero_right] using hzP i
  let hincrement :
      ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius :=
    fun j => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [reflectedCauchyIncrement_left]
        simpa using hzlt i
      · rw [reflectedCauchyIncrement_right]
        exact hzlt i
  let E :=
    D.atIncrement (reflectedCauchyIncrement z) hincrement
  let S :=
    PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
      f directions z
  have C : ReflectedSourceCauchyCompatibility OS S E := by
    simpa [S, E] using hcompat z hincrement
  have hcoeff :
      ∀ p r,
        positiveTimeTaylorScalarGram OS n
            (T.homogeneousSource z) p r =
          E.scalarGram p r := by
    intro p r
    change
      positiveTimeTaylorScalarGram OS n S.homogeneousSource p r =
        E.scalarGram p r
    exact
      S.positiveTimeTaylorScalarGram_homogeneousSource_eq_cauchyScalarGram
        OS E C p r
  have hmulti :
      HasSum E.multiIndexTerm
        (D.scalar (D.center + reflectedCauchyIncrement z)) := by
    apply E.hasSum_multiIndexTerm_of_cauchyPowerSeries
    simpa [E, ReflectedCauchyPolydiscData.atIncrement] using hxsum
  have hgram :
      HasSum (fun pq : ℕ × ℕ => E.scalarGram pq.1 pq.2)
        (D.scalar (D.center + reflectedCauchyIncrement z)) :=
    E.hasSum_scalarGram hmulti
  have hsquareE :
      Tendsto
        (fun N =>
          ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
            E.scalarGram pq.1 pq.2)
        atTop
        (nhds (D.scalar
          (D.center + reflectedCauchyIncrement z))) :=
    E.tendsto_square_sum_scalarGram hgram
  let G :=
    positiveTimeTaylorGramData OS n (T.homogeneousSource z)
  have hΨz :
      Tendsto (fun N => T.partialSum OS N z) atTop (𝓝 (Ψ z)) :=
    hΨ.tendsto_at hzP
  have hG :
      Tendsto G.partialSum atTop (𝓝 (Ψ z)) := by
    convert hΨz using 1
    funext N
    exact (T.partialSum_eq_gramData OS N z).symm
  have hsquareG :
      Tendsto
        (fun N =>
          ∑ pq ∈ Finset.range N ×ˢ Finset.range N,
            G.scalarGram pq.1 pq.2)
        atTop
        (nhds (D.scalar
          (D.center + reflectedCauchyIncrement z))) := by
    convert hsquareE using 1
    funext N
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [G, positiveTimeTaylorGramData_scalarGram]
    exact hcoeff pq.1 pq.2
  exact G.norm_limit_sq_eq_re_of_tendsto_squareSum
    (Ψ z) (D.scalar (D.center + reflectedCauchyIncrement z))
    hG hsquareG

/-- Explicit-radius form of the norm-square reflected scalar identity. The
Cauchy contour radius is `D.radius`, while `Rw` is a larger holomorphy radius;
the resulting numerical norm bound is independent of the source data. -/
theorem norm_sq_holomorphicField_eq_reflectedScalar_of_compatibility_of_norm_lt
    {d n q : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin (q + 1) → NPointDomain d n)
    (D : ReflectedCauchyPolydiscData (q + 1))
    (hcompat :
      ∀ (z : Fin (q + 1) → ℂ)
        (hincrement :
          ∀ i, ‖reflectedCauchyIncrement z i‖ < D.radius),
        ReflectedSourceCauchyCompatibility OS
          (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
            f directions z)
          (D.atIncrement (reflectedCauchyIncrement z) hincrement))
    (Rw : ℝ)
    (hRw : D.radius < Rw)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRwU :
      SCV.closedPolydisc D.center (fun _ => Rw) ⊆ U)
    (hscalar : DifferentiableOn ℂ D.scalar U)
    (Ψ : (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          f directions).partialSum OS)
        Ψ atTop
        (SCV.Polydisc
          (0 : Fin (q + 1) → ℂ) (fun _ => D.radius)))
    (z : Fin (q + 1) → ℂ)
    (hzP :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => D.radius))
    (hz :
      ‖reflectedCauchyIncrement z‖ <
        D.radius /
          (2 * ((((q + 1) + (q + 1) - 1 : ℕ) : ℝ) + 2))) :
    ‖Ψ z‖ ^ 2 =
      (D.scalar (D.center + reflectedCauchyIncrement z)).re := by
  apply
    norm_sq_holomorphicField_eq_reflectedScalar_of_compatibility_of_hasSum
      OS f directions D hcompat Ψ hΨ z hzP
  simpa using
    SCV.hasSum_cauchyPowerSeriesPolydisc_diag_of_differentiableOn
      D.radius_pos hRw hU hRwU hscalar hz

/-- A common Cauchy contour and larger holomorphy polydisc give one real
parameter neighborhood on which every Hilbert field in a source family has
the reflected scalar norm square. No uniform scalar boundary bound is
required; those bounds may vary with the source. -/
theorem eventually_norm_sq_holomorphicField_eq_reflectedScalar_family_of_compatibility
    {d n q : ℕ} [NeZero d]
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) n)
    (directions : Fin (q + 1) → NPointDomain d n)
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (R Rw : ℝ)
    (hR : 0 < R)
    (hcenter : ∀ a, (D a).center = 0)
    (hradius : ∀ a, (D a).radius = R)
    (hRw : R < Rw)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRwU :
      SCV.closedPolydisc
          (0 : Fin ((q + 1) + (q + 1)) → ℂ) (fun _ => Rw) ⊆ U)
    (hscalar : ∀ a, DifferentiableOn ℂ (D a).scalar U)
    (hcompat :
      ∀ a (z : Fin (q + 1) → ℂ)
        (hincrement :
          ∀ i, ‖reflectedCauchyIncrement z i‖ < (D a).radius),
        ReflectedSourceCauchyCompatibility OS
          (PositiveTimeSourceCoefficientData.ofNormalizedDerivatives
            (f a) directions z)
          ((D a).atIncrement
            (reflectedCauchyIncrement z) hincrement))
    (Ψ : ι → (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      ∀ a,
        TendstoLocallyUniformlyOn
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            (f a) directions).partialSum OS)
          (Ψ a) atTop
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius))) :
    ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
      ∀ a,
        ‖Ψ a (fun i => (x i : ℂ))‖ ^ 2 =
          ((D a).scalar
            ((D a).center +
              reflectedCauchyIncrement (fun i => (x i : ℂ)))).re := by
  let cauchyDimension : ℕ := (q + 1) + (q + 1) - 1
  let bound : ℝ :=
    R / (2 * ((cauchyDimension : ℝ) + 2))
  have hdenom : 0 < 2 * ((cauchyDimension : ℝ) + 2) := by
    positivity
  have hbound : 0 < bound := div_pos hR hdenom
  have hboundR : bound < R := by
    dsimp [bound]
    rw [div_lt_iff₀ hdenom]
    have hc : 0 ≤ (cauchyDimension : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hembed_cont :
      Continuous
        (fun x : Fin (q + 1) → ℝ => fun i => (x i : ℂ)) := by
    fun_prop
  have hsmall :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ‖(fun i => (x i : ℂ))‖ < bound := by
    have hball :
        Metric.ball (0 : Fin (q + 1) → ℂ) bound ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ hbound
    have hevent := hembed_cont.continuousAt.eventually hball
    simpa [Metric.mem_ball, dist_zero_right] using hevent
  filter_upwards [hsmall] with x hx
  intro a
  let z : Fin (q + 1) → ℂ := fun i => (x i : ℂ)
  have hreflected_le :
      ‖reflectedCauchyIncrement z‖ ≤ ‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [reflectedCauchyIncrement_left]
      simpa using norm_le_pi_norm z i
    · rw [reflectedCauchyIncrement_right]
      exact norm_le_pi_norm z i
  have hreflected :
      ‖reflectedCauchyIncrement z‖ <
        (D a).radius /
          (2 * ((((q + 1) + (q + 1) - 1 : ℕ) : ℝ) + 2)) := by
    rw [hradius a]
    exact hreflected_le.trans_lt (by simpa [z, bound, cauchyDimension] using hx)
  have hzP :
      z ∈ SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius) := by
    intro i
    change dist (z i) 0 < (D a).radius
    rw [dist_zero_right, hradius a]
    exact (norm_le_pi_norm z i).trans_lt
      (hx.trans hboundR)
  apply
    norm_sq_holomorphicField_eq_reflectedScalar_of_compatibility_of_norm_lt
      OS (f a) directions (D a) (hcompat a)
      Rw (by simpa [hradius a] using hRw)
      hU
      (by simpa [hcenter a] using hRwU)
      (hscalar a) (Ψ a) (hΨ a) z hzP hreflected

/-- A compact strict-positive difference-time carrier is stable under all
sufficiently small simultaneous chronological source translations. -/
theorem eventually_chronologicalParameterTranslate_tsupport_subset_orderedPositive
    {d k : ℕ} [NeZero d]
    (f : SchwartzNPoint d (k + 1))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f) :
    ∀ᶠ u : Fin k → ℝ in 𝓝 0,
      tsupport
          ((translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun i : Fin k =>
                chronologicalTimeSourceDirection (d := d) i) u)
            f : SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (k + 1) := by
  obtain ⟨ε, hε_pos, _hbase, hmargin⟩ :=
    eventually_chronologicalParameterTranslate_uniform_positive_margin f hf
  filter_upwards [hmargin] with u hu
  intro x hx
  have htranslated :
      ∀ j : Fin (k + 1),
        ε ≤ section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) j :=
    hu x hx
  have htime_pos : ∀ j : Fin (k + 1),
      0 < section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1) x) j := by
    intro j
    exact hε_pos.trans_le (htranslated j)
  have hδ_pos' :
      ∀ j : Fin (k + 1), 0 < (section43DiffCoordRealCLE d (k + 1) x) j 0 := by
    intro j
    simpa [section43QTime, nPointTimeSpatialCLE] using htime_pos j
  have hordered :=
    section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
      d (k + 1) (δ := section43DiffCoordRealCLE d (k + 1) x) hδ_pos'
  simpa using hordered

/-- A common compact difference-time carrier gives one chronological
translation neighborhood on which every source in the family remains
strictly ordered in positive Euclidean time. -/
theorem eventually_chronologicalParameterTranslate_family_tsupport_subset_orderedPositive
    {d k : ℕ} [NeZero d]
    {ι : Type*}
    (f : ι → SchwartzNPoint d (k + 1))
    (hf : HasUniformCompactStrictPositiveDifferenceTimeSupport f) :
    ∀ᶠ u : Fin k → ℝ in 𝓝 0,
      ∀ a,
        tsupport
            ((translateSchwartzConfiguration
              (sourceParameterDisplacementCLM
                (fun i : Fin k =>
                  chronologicalTimeSourceDirection (d := d) i) u)
              (f a) : SchwartzNPoint d (k + 1)) :
                NPointDomain d (k + 1) → ℂ) ⊆
          OrderedPositiveTimeRegion d (k + 1) := by
  obtain ⟨ε, hε_pos, _hbase, hmargin⟩ :=
    eventually_chronologicalParameterTranslate_family_uniform_positive_margin
      f hf
  filter_upwards [hmargin] with u hu
  intro a x hx
  have htranslated :
      ∀ j : Fin (k + 1),
        ε ≤ section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) j :=
    hu a x hx
  have htime_pos :
      ∀ j : Fin (k + 1),
        0 < section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) j := by
    intro j
    exact hε_pos.trans_le (htranslated j)
  have hδ_pos' :
      ∀ j : Fin (k + 1),
        0 < (section43DiffCoordRealCLE d (k + 1) x) j 0 := by
    intro j
    simpa [section43QTime, nPointTimeSpatialCLE] using htime_pos j
  have hordered :=
    section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
      d (k + 1) (δ := section43DiffCoordRealCLE d (k + 1) x) hδ_pos'
  simpa using hordered

/-- Near zero, a compact-time positive source's chronological parameter germ
is the genuine configuration translation. -/
theorem eventually_localPositiveTimeParameterTranslate_chronological_coe_eq
    {d k : ℕ} [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) (k + 1))
    (hf : HasCompactStrictPositiveDifferenceTimeSupport f.1) :
    (fun u : Fin k → ℝ =>
      (localPositiveTimeParameterTranslate f
        (fun i : Fin k =>
          chronologicalTimeSourceDirection (d := d) i) u).1) =ᶠ[𝓝 0]
      (fun u =>
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          f.1) := by
  filter_upwards
    [eventually_chronologicalParameterTranslate_tsupport_subset_orderedPositive
      f.1 hf] with u hu
  simp only [localPositiveTimeParameterTranslate]
  rw [dif_pos hu]

/-- Near zero, every member of a compact-time positive-source family has the
same genuine chronological configuration-translation formula. -/
theorem eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
    {d k : ℕ} [NeZero d]
    {ι : Type*}
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (k + 1))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1)) :
    ∀ᶠ u : Fin k → ℝ in 𝓝 0,
      ∀ a,
        (localPositiveTimeParameterTranslate (f a)
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u).1 =
          translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun i : Fin k =>
                chronologicalTimeSourceDirection (d := d) i) u)
            (f a).1 := by
  filter_upwards
    [eventually_chronologicalParameterTranslate_family_tsupport_subset_orderedPositive
      (fun a => (f a).1) hf] with u hu
  intro a
  simp only [localPositiveTimeParameterTranslate]
  rw [dif_pos (hu a)]

/-- Uniform family form of the diagonal norm argument. Once the reflected
scalar norm identity, scalar real edge, and genuine source translation all
hold on common neighborhoods, the honest positive-time vector norm identity
holds on one common neighborhood as well. -/
theorem eventually_norm_sq_holomorphicField_eq_chronologicalTranslate_family
    {d q : ℕ} [NeZero d]
    {ι : Type*}
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (Ψ : ι → (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hnorm :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ∀ a,
          ‖Ψ a (fun i => (x i : ℂ))‖ ^ 2 =
            ((D a).scalar
              ((D a).center +
                reflectedCauchyIncrement (fun i => (x i : ℂ)))).re)
    (hsource :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ∀ a,
          (localPositiveTimeParameterTranslate (f a)
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i) x).1 =
            translateSchwartzConfiguration
              (sourceParameterDisplacementCLM
                (fun i : Fin (q + 1) =>
                  chronologicalTimeSourceDirection (d := d) i) x)
              (f a).1)
    (hreal :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice (D a).scalar (D a).center u =
            OS.S ((q + 2) + (q + 2))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM
                    (fun i : Fin (q + 1) =>
                      chronologicalTimeSourceDirection (d := d) i) u)
                  ((f a).1.osConjTensorProduct (f a).1)))) :
    ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
      ∀ a,
        ‖Ψ a (fun i => (x i : ℂ))‖ ^ 2 =
          ‖osiiPositiveTimeSingleVectorCLM OS (q + 2)
            (localPositiveTimeParameterTranslate (f a)
              (fun i : Fin (q + 1) =>
                chronologicalTimeSourceDirection (d := d) i) x)‖ ^ 2 := by
  let directions : Fin (q + 1) → NPointDomain d (q + 2) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  let diag :
      (Fin (q + 1) → ℝ) →
        (Fin ((q + 1) + (q + 1)) → ℝ) :=
    fun x => Fin.append x x
  have hdiag_cont : Continuous diag := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [diag, Fin.append_left]
      fun_prop
    · simp only [diag, Fin.append_right]
      fun_prop
  have hdiag_zero : diag (0 : Fin (q + 1) → ℝ) = 0 := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [diag]
    · change
        Fin.append (0 : Fin (q + 1) → ℝ) 0
            (Fin.natAdd (q + 1) i) =
          0
      rw [Fin.append_right]
      rfl
  have hdiag_tendsto :
      Tendsto diag
        (𝓝 (0 : Fin (q + 1) → ℝ))
        (𝓝 (0 : Fin ((q + 1) + (q + 1)) → ℝ)) := by
    have ht :
        Tendsto diag
          (𝓝 (0 : Fin (q + 1) → ℝ))
          (𝓝 (diag (0 : Fin (q + 1) → ℝ))) :=
      hdiag_cont.continuousAt
    rw [hdiag_zero] at ht
    exact ht
  have hreal_diag := hdiag_tendsto.eventually hreal
  filter_upwards [hnorm, hsource, hreal_diag]
      with x hxnorm hxsource hxreal
  intro a
  rw [hxnorm a]
  rw [osiiPositiveTimeSingleVectorCLM_norm_sq]
  rw [show
      (localPositiveTimeParameterTranslate (f a) directions x).1 =
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM directions x) (f a).1 by
      exact hxsource a]
  have hincrement :
      realCoordinateEmbeddingCLM ((q + 1) + (q + 1)) (diag x) =
        reflectedCauchyIncrement (fun i => (x i : ℂ)) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [diag]
    · rw [realCoordinateEmbeddingCLM_apply,
        reflectedCauchyIncrement_right]
      change
        ((Fin.append x x (Fin.natAdd (q + 1) i) : ℝ) : ℂ) =
          (x i : ℂ)
      rw [Fin.append_right]
  have hdiag_left :
      (fun i : Fin (q + 1) => diag x (Fin.castAdd (q + 1) i)) = x := by
    funext i
    simp [diag]
  have hdiag_right :
      (fun i : Fin (q + 1) => diag x (Fin.natAdd (q + 1) i)) = x := by
    funext i
    change Fin.append x x (Fin.natAdd (q + 1) i) = x i
    exact Fin.append_right x x i
  have hdisplacement :
      reflectedSourceParameterDisplacementCLM directions (diag x) =
        Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM directions x))
          (sourceParameterDisplacementCLM directions x) := by
    change
      Fin.append
          (timeReflectionN d
            (sourceParameterDisplacementCLM directions
              (fun i => diag x (Fin.castAdd (q + 1) i))))
          (sourceParameterDisplacementCLM directions
            (fun i => diag x (Fin.natAdd (q + 1) i))) =
        _
    rw [hdiag_left, hdiag_right]
  rw [osConjTensorProduct_translateSchwartzConfiguration]
  rw [← hdisplacement]
  rw [← hxreal a]
  simp only [realAffineSlice, hincrement]

/-- Uniform compact-time family real edge. One time carrier supplies one raw
cutoff germ, and the explicit-radius family norm theorem supplies the common
analytic neighborhood needed by the mixed-pairing argument. -/
theorem eventually_holomorphicField_eq_chronologicalTranslate_family_compactTime
    {d q : ℕ} [NeZero d]
    {ι : Type*}
    (hTowerC : IsScalarTower ℝ ℂ ℂ)
    (OS : OsterwalderSchraderAxioms d)
    (f : ι → euclideanPositiveTimeSubmodule (d := d) (q + 2))
    (hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1))
    (D : ι → ReflectedCauchyPolydiscData (q + 1))
    (R : ℝ)
    (hR : 0 < R)
    (hradius : ∀ a, (D a).radius = R)
    {U : Set (Fin ((q + 1) + (q + 1)) → ℂ)}
    (hU : IsOpen U)
    (hRU :
      ∀ a,
        SCV.closedPolydisc (D a).center (fun _ => (D a).radius) ⊆ U)
    (hscalar : ∀ a, DifferentiableOn ℂ (D a).scalar U)
    (hreal :
      ∀ᶠ x : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          realAffineSlice (D a).scalar (D a).center x =
            OS.S ((q + 2) + (q + 2))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM
                    (fun i : Fin (q + 1) =>
                      chronologicalTimeSourceDirection (d := d) i) x)
                  ((f a).1.osConjTensorProduct (f a).1))))
    (Ψ : ι → (Fin (q + 1) → ℂ) → OSHilbertSpace OS)
    (hΨ :
      ∀ a,
        TendstoLocallyUniformlyOn
          ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
            (f a)
            (fun i : Fin (q + 1) =>
              chronologicalTimeSourceDirection (d := d) i)).partialSum OS)
          (Ψ a) atTop
          (SCV.Polydisc
            (0 : Fin (q + 1) → ℂ) (fun _ => (D a).radius)))
    (hnorm :
      ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
        ∀ a,
          ‖Ψ a (fun i => (x i : ℂ))‖ ^ 2 =
            ‖osiiPositiveTimeSingleVectorCLM OS (q + 2)
              (localPositiveTimeParameterTranslate (f a)
                (fun i : Fin (q + 1) =>
                  chronologicalTimeSourceDirection (d := d) i) x)‖ ^ 2) :
    ∀ᶠ x : Fin (q + 1) → ℝ in 𝓝 0,
      ∀ a,
        Ψ a (fun i => (x i : ℂ)) =
          osiiPositiveTimeSingleVectorCLM OS (q + 2)
            (localPositiveTimeParameterTranslate (f a)
              (fun i : Fin (q + 1) =>
                chronologicalTimeSourceDirection (d := d) i) x) := by
  let directions : Fin (q + 1) → NPointDomain d (q + 2) :=
    fun i => chronologicalTimeSourceDirection (d := d) i
  let source : ι → SchwartzNPoint d (q + 2) :=
    fun a => (f a).1
  let φ : ι → SchwartzNPoint d ((q + 2) + (q + 2)) :=
    fun a => (source a).osConjTensorProduct (source a)
  obtain ⟨ε, hε, hχ_growth, hχ_disj, _hχ_base, hχ_local⟩ :=
    exists_twoBlockTimeMarginCutoff_one_on_reflectedTranslation_family_germ
      source (by simpa [source] using hf)
  let χ : NPointDomain d ((q + 2) + (q + 2)) → ℂ :=
    osiiA0TwoBlockTimeMarginCutoff d (q + 2) ε
  let T : SchwartzNPoint d ((q + 2) + (q + 2)) →L[ℂ] ℂ :=
    osiiA0TemperateCutoffSchwingerCLM OS χ hχ_growth hχ_disj
  have hlocal_one :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a y, y ∈ tsupport
          ((translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions u) (φ a) :
              SchwartzNPoint d ((q + 2) + (q + 2))) :
                NPointDomain d ((q + 2) + (q + 2)) → ℂ) →
          χ y = 1 := by
    simpa [directions, φ, source, χ] using hχ_local
  have hlocal_eval :
      ∀ᶠ u : Fin ((q + 1) + (q + 1)) → ℝ in 𝓝 0,
        ∀ a,
          T (translateSchwartzConfiguration
            (reflectedSourceParameterDisplacementCLM directions u) (φ a)) =
            OS.S ((q + 2) + (q + 2))
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (reflectedSourceParameterDisplacementCLM directions u)
                  (φ a))) := by
    filter_upwards [hlocal_one] with u hu
    intro a
    let ψ : SchwartzNPoint d ((q + 2) + (q + 2)) :=
      translateSchwartzConfiguration
        (reflectedSourceParameterDisplacementCLM directions u) (φ a)
    have hψ_disj :
        Disjoint
          (tsupport
            ((ψ : SchwartzNPoint d ((q + 2) + (q + 2))) :
              NPointDomain d ((q + 2) + (q + 2)) → ℂ))
          (CoincidenceLocus d ((q + 2) + (q + 2))) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hcoin
      have hχx : χ x = 1 := hu a x (by simpa [ψ] using hx)
      have hx_support : x ∈ Function.support χ := by
        intro hxzero
        rw [hxzero] at hχx
        norm_num at hχx
      exact Set.disjoint_left.mp hχ_disj (subset_closure hx_support) hcoin
    have hψ_zero : VanishesToInfiniteOrderOnCoincidence ψ :=
      VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
        (f := ψ) hψ_disj
    simpa [T, ψ] using
      osiiA0TemperateCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
        OS χ hχ_growth hχ_disj ψ hψ_zero (hu a)
  have hsource :=
    eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      f hf
  apply
    eventually_holomorphicField_eq_localPositiveTimeParameterTranslate_family_of_cutoffData
      hTowerC OS f directions D R hR hradius hU hRU hscalar hreal
      Ψ (by simpa [directions] using hΨ) χ T
  · simpa [directions, φ, source] using hlocal_one
  · simpa [directions, φ, source] using hlocal_eval
  · simpa [directions] using hsource
  · simpa [directions] using hnorm
  · intro a g hχ_one hgf_disj z p
    exact
      osiiA0TemperateCutoffSchwingerCLM_homogeneousSource_eq
        OS directions g (f a) χ hχ_growth hχ_disj
        hχ_one hgf_disj z p

end OSIIChapterV
end OSReconstruction
