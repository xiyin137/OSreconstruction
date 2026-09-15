/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
import OSReconstruction.SCV.ProductDensity












noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

@[simp] private theorem finAppendCLE_symm_fst_apply
    (n m : ℕ) (x : Fin (n + m) → ℝ) (i : Fin n) :
    ((SCV.finAppendCLE n m).symm x).1 i = splitFirst n m x i := by
  have h := congrFun (SCV.finAppendCLE_append_symm x) (Fin.castAdd m i)
  simpa [splitFirst, Fin.append_left] using h

@[simp] private theorem finAppendCLE_symm_snd_apply
    (n m : ℕ) (x : Fin (n + m) → ℝ) (j : Fin m) :
    ((SCV.finAppendCLE n m).symm x).2 j = splitLast n m x j := by
  have h := congrFun (SCV.finAppendCLE_append_symm x) (Fin.natAdd n j)
  simpa [splitLast, Fin.append_right] using h

private theorem twoBlockProductSchwartz_apply_split
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin (n + m) → ℝ) :
    SCV.twoBlockProductSchwartz η₁ η₂ x =
      η₁ (splitFirst n m x) * η₂ (splitLast n m x) := by
  have hx :
      x = Fin.append (splitFirst n m x) (splitLast n m x) := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [splitFirst, Fin.append_left]
    · intro j
      simp [splitLast, Fin.append_right]
  rw [hx]
  simp [SCV.twoBlockProductSchwartz_apply]

theorem twoBlockProductSchwartz_tsupport_subset
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport (SCV.twoBlockProductSchwartz η₁ η₂ :
        (Fin (n + m) → ℝ) → ℂ) ⊆
      (splitFirst n m) ⁻¹' tsupport (η₁ : (Fin n → ℝ) → ℂ) ∩
        (splitLast n m) ⁻¹' tsupport (η₂ : (Fin m → ℝ) → ℂ) := by
  refine closure_minimal ?_ <|
    ((isClosed_tsupport _).preimage (splitFirst_continuousLinear n m)).inter
      ((isClosed_tsupport _).preimage (splitLast_continuousLinear n m))
  intro x hx
  have hxne :
      η₁ (splitFirst n m x) * η₂ (splitLast n m x) ≠ 0 := by
    simpa [Function.mem_support, twoBlockProductSchwartz_apply_split] using hx
  constructor
  · change splitFirst n m x ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ)
    apply subset_tsupport
    intro hzero
    exact hxne (by simp [hzero])
  · change splitLast n m x ∈ tsupport (η₂ : (Fin m → ℝ) → ℂ)
    apply subset_tsupport
    intro hzero
    exact hxne (by simp [hzero])

/-- A two-block product has compact support when both block tests do. -/
theorem twoBlockProductSchwartz_hasCompactSupport
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₁ : HasCompactSupport (η₁ : (Fin n → ℝ) → ℂ))
    (hη₂ : HasCompactSupport (η₂ : (Fin m → ℝ) → ℂ)) :
    HasCompactSupport
      (SCV.twoBlockProductSchwartz η₁ η₂ :
        (Fin (n + m) → ℝ) → ℂ) := by
  have hproduct :
      HasCompactSupport
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          η₁ p.1 * η₂ p.2) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hη₁.isCompact.prod hη₂.isCompact) ?_
    intro p hp
    have hpne : η₁ p.1 * η₂ p.2 ≠ 0 := hp
    constructor
    · apply subset_tsupport
      intro hzero
      exact hpne (by simp [hzero])
    · apply subset_tsupport
      intro hzero
      exact hpne (by simp [hzero])
  have hcomp :=
    hproduct.comp_homeomorph
      (SCV.finAppendCLE n m).symm.toHomeomorph
  have hfun :
      (SCV.twoBlockProductSchwartz η₁ η₂ :
          (Fin (n + m) → ℝ) → ℂ) =
        fun x =>
          η₁ (((SCV.finAppendCLE n m).symm x).1) *
            η₂ (((SCV.finAppendCLE n m).symm x).2) := by
    funext x
    let p := (SCV.finAppendCLE n m).symm x
    have hx : x = Fin.append p.1 p.2 := by
      exact (SCV.finAppendCLE_append_symm x).symm
    rw [hx, SCV.twoBlockProductSchwartz_apply]
    simp [p]
  rw [hfun]
  simpa [Function.comp_def] using hcomp

/-- The ordinary Schwartz tensor product has compact support when both
factors do. -/
theorem SchwartzMap.tensorProduct_hasCompactSupport
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₁ : HasCompactSupport (η₁ : (Fin n → ℝ) → ℂ))
    (hη₂ : HasCompactSupport (η₂ : (Fin m → ℝ) → ℂ)) :
    HasCompactSupport
      (η₁.tensorProduct η₂ :
        (Fin (n + m) → ℝ) → ℂ) := by
  have heq :
      (η₁.tensorProduct η₂ :
        (Fin (n + m) → ℝ) → ℂ) =
        (SCV.twoBlockProductSchwartz η₁ η₂ :
          (Fin (n + m) → ℝ) → ℂ) := by
    funext x
    rw [SchwartzMap.tensorProduct_apply,
      twoBlockProductSchwartz_apply_split]
  rw [heq]
  exact twoBlockProductSchwartz_hasCompactSupport
    n m η₁ η₂ hη₁ hη₂

/-- Ordinary scalar difference coordinates, obtained from the existing
one-dimensional spacetime difference chart. -/
noncomputable def section43ScalarDiffCLE (n : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (section43TimeAsOnePointCLE n).trans
    ((BHW.realDiffCoordCLE n 0).trans
      (section43TimeAsOnePointCLE n).symm)

@[simp] theorem section43ScalarDiffCLE_apply
    (n : ℕ) (x : Fin n → ℝ) (k : Fin n) :
    section43ScalarDiffCLE n x k =
      if _hk : k.val = 0 then x k
      else x k - x ⟨k.val - 1, by omega⟩ := by
  simp [section43ScalarDiffCLE, BHW.realDiffCoordCLE_apply]

@[simp] theorem section43ScalarDiffCLE_symm_apply
    (n : ℕ) (δ : Fin n → ℝ) (k : Fin n) :
    (section43ScalarDiffCLE n).symm δ k =
      ∑ j : Fin (k.val + 1), δ ⟨j.val, by omega⟩ := by
  simp [section43ScalarDiffCLE, BHW.realDiffCoordCLE_symm_apply]

/-- Positive scalar differences have positive cumulative absolute times. -/
theorem section43ScalarDiffCLE_symm_pos
    {n : ℕ} {δ : Fin n → ℝ}
    (hδ : ∀ i, 0 < δ i) (i : Fin n) :
    0 < (section43ScalarDiffCLE n).symm δ i := by
  rw [section43ScalarDiffCLE_symm_apply, Finset.sum_fin_eq_sum_range]
  have hnonempty : (Finset.range (i.val + 1)).Nonempty := ⟨0, by simp⟩
  refine Finset.sum_pos ?_ hnonempty
  intro r hr
  have hrlt : r < i.val + 1 := Finset.mem_range.mp hr
  simpa [hrlt] using hδ ⟨r, by omega⟩

/-- Positive scalar differences have strictly increasing cumulative absolute
times. -/
theorem section43ScalarDiffCLE_symm_strictMono
    {n : ℕ} {δ : Fin n → ℝ}
    (hδ : ∀ i, 0 < δ i) :
    StrictMono ((section43ScalarDiffCLE n).symm δ) := by
  intro i j hij
  rw [section43ScalarDiffCLE_symm_apply,
    section43ScalarDiffCLE_symm_apply]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have hijv : i.val < j.val := hij
  have hle : i.val + 1 ≤ j.val + 1 := Nat.succ_le_succ hijv.le
  let fj : ℕ → ℝ := fun r =>
    if h : r < j.val + 1 then
      δ ⟨(⟨r, h⟩ : Fin (j.val + 1)).val, by omega⟩
    else 0
  have hblock_nonempty :
      (Finset.Ico (i.val + 1) (j.val + 1)).Nonempty :=
    ⟨i.val + 1, Finset.mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ hijv⟩⟩
  have hleft :
      (∑ r ∈ Finset.range (i.val + 1),
        if h : r < i.val + 1 then
          δ ⟨(⟨r, h⟩ : Fin (i.val + 1)).val, by omega⟩
        else 0) =
      ∑ r ∈ Finset.range (i.val + 1), fj r := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hri : r < i.val + 1 := Finset.mem_range.mp hr
    have hrj : r < j.val + 1 := lt_of_lt_of_le hri hle
    have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
    rw [dif_pos hri]
    simp [fj, hrjle]
  have hblock_pos :
      0 < ∑ r ∈ Finset.Ico (i.val + 1) (j.val + 1), fj r := by
    refine Finset.sum_pos ?_ hblock_nonempty
    intro r hr
    have hrj : r < j.val + 1 := (Finset.mem_Ico.mp hr).2
    have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
    simpa [fj, hrjle] using hδ ⟨r, by omega⟩
  rw [hleft]
  change (∑ r ∈ Finset.range (i.val + 1), fj r) <
    ∑ r ∈ Finset.range (j.val + 1), fj r
  rw [← Finset.sum_range_add_sum_Ico fj hle]
  exact lt_add_of_pos_right _ hblock_pos

/-- Apply scalar difference coordinates separately to the left and right
blocks of one appended tuple. -/
noncomputable def osiiAxisPairBlockwiseTimeDiffCLE (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃L[ℝ] (Fin (n + m) → ℝ) :=
  (SCV.finAppendCLE n m).symm |>.trans
    ((ContinuousLinearEquiv.prodCongr
      (section43ScalarDiffCLE n)
      (section43ScalarDiffCLE m)).trans
        (SCV.finAppendCLE n m))

@[simp] theorem osiiAxisPairBlockwiseTimeDiffCLE_apply_left
    (n m : ℕ) (x : Fin (n + m) → ℝ) (i : Fin n) :
    osiiAxisPairBlockwiseTimeDiffCLE n m x (Fin.castAdd m i) =
      section43ScalarDiffCLE n (splitFirst n m x) i := by
  simp [osiiAxisPairBlockwiseTimeDiffCLE]

@[simp] theorem osiiAxisPairBlockwiseTimeDiffCLE_apply_right
    (n m : ℕ) (x : Fin (n + m) → ℝ) (j : Fin m) :
    osiiAxisPairBlockwiseTimeDiffCLE n m x (Fin.natAdd n j) =
      section43ScalarDiffCLE m (splitLast n m x) j := by
  simp [osiiAxisPairBlockwiseTimeDiffCLE]

@[simp] theorem osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left
    (n m : ℕ) (δ : Fin (n + m) → ℝ) (i : Fin n) :
    (osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ
        (Fin.castAdd m i) =
      (section43ScalarDiffCLE n).symm (splitFirst n m δ) i := by
  have h :
      splitFirst n m ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ) =
        (section43ScalarDiffCLE n).symm (splitFirst n m δ) := by
    apply (section43ScalarDiffCLE n).injective
    ext k
    rw [(section43ScalarDiffCLE n).apply_symm_apply]
    calc
      section43ScalarDiffCLE n
          (splitFirst n m ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ)) k =
          osiiAxisPairBlockwiseTimeDiffCLE n m
            ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ)
            (Fin.castAdd m k) := by
              symm
              exact osiiAxisPairBlockwiseTimeDiffCLE_apply_left n m _ k
      _ = δ (Fin.castAdd m k) := by
        exact congrFun
          ((osiiAxisPairBlockwiseTimeDiffCLE n m).apply_symm_apply δ)
          (Fin.castAdd m k)
      _ = splitFirst n m δ k := by rfl
  exact congrFun h i

@[simp] theorem osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right
    (n m : ℕ) (δ : Fin (n + m) → ℝ) (j : Fin m) :
    (osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ
        (Fin.natAdd n j) =
      (section43ScalarDiffCLE m).symm (splitLast n m δ) j := by
  have h :
      splitLast n m ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ) =
        (section43ScalarDiffCLE m).symm (splitLast n m δ) := by
    apply (section43ScalarDiffCLE m).injective
    ext k
    rw [(section43ScalarDiffCLE m).apply_symm_apply]
    calc
      section43ScalarDiffCLE m
          (splitLast n m ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ)) k =
          osiiAxisPairBlockwiseTimeDiffCLE n m
            ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ)
            (Fin.natAdd n k) := by
              symm
              exact osiiAxisPairBlockwiseTimeDiffCLE_apply_right n m _ k
      _ = δ (Fin.natAdd n k) := by
        exact congrFun
          ((osiiAxisPairBlockwiseTimeDiffCLE n m).apply_symm_apply δ)
          (Fin.natAdd n k)
      _ = splitLast n m δ k := by rfl
  exact congrFun h j

/-- Chronologically reverse and time-reflect the left absolute-time block,
while leaving the right block fixed. -/
noncomputable def osiiAxisPairReflectReverseLeftTimeCLE (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃L[ℝ] (Fin (n + m) → ℝ) :=
  (SCV.finAppendCLE n m).symm |>.trans
    ((ContinuousLinearEquiv.prodCongr
      ((LinearEquiv.funCongrLeft ℝ ℝ Fin.revPerm).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.neg ℝ))
      (ContinuousLinearEquiv.refl ℝ (Fin m → ℝ))).trans
        (SCV.finAppendCLE n m))

@[simp] theorem osiiAxisPairReflectReverseLeftTimeCLE_apply_left
    (n m : ℕ) (x : Fin (n + m) → ℝ) (i : Fin n) :
    osiiAxisPairReflectReverseLeftTimeCLE n m x (Fin.castAdd m i) =
      -x (Fin.castAdd m (Fin.rev i)) := by
  simp [osiiAxisPairReflectReverseLeftTimeCLE,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, splitFirst]

@[simp] theorem osiiAxisPairReflectReverseLeftTimeCLE_apply_right
    (n m : ℕ) (x : Fin (n + m) → ℝ) (j : Fin m) :
    osiiAxisPairReflectReverseLeftTimeCLE n m x (Fin.natAdd n j) =
      x (Fin.natAdd n j) := by
  simp [osiiAxisPairReflectReverseLeftTimeCLE, splitLast]

/-- Linear part of the passage from separate left/right difference times to
the single global chronological difference-time chart. -/
noncomputable def osiiAxisPairBlockGlobalTimeCLE (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃L[ℝ] (Fin (n + m) → ℝ) :=
  (osiiAxisPairBlockwiseTimeDiffCLE n m).symm |>.trans
    ((osiiAxisPairReflectReverseLeftTimeCLE n m).trans
      (section43ScalarDiffCLE (n + m)))

/-- The affine displacement in global difference coordinates: a common shift
changes the first coordinate, while shifting the right block changes only the
cross-block gap. -/
def osiiAxisPairGlobalTimeDiffShift
    (n m : ℕ) (s t : ℝ) : Fin (n + m) → ℝ :=
  fun k =>
    (if k.val = 0 then s else 0) +
      (if k.val = n ∧ 0 < m then t else 0)

/-- The corresponding shift in absolute chronological time coordinates. -/
def osiiAxisPairGlobalAbsoluteTimeShift
    (n m : ℕ) (s t : ℝ) : Fin (n + m) → ℝ :=
  fun k => if k.val < n then s else s + t

/-- Passing the absolute block shift to global differences leaves only the
first-coordinate common shift and the cross-block gap shift. -/
theorem section43ScalarDiffCLE_globalAbsoluteTimeShift
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (s t : ℝ) :
    section43ScalarDiffCLE (n + m)
        (osiiAxisPairGlobalAbsoluteTimeShift n m s t) =
      osiiAxisPairGlobalTimeDiffShift n m s t := by
  ext k
  rw [section43ScalarDiffCLE_apply]
  by_cases hk0 : k.val = 0
  · have h0n : 0 ≠ n := by omega
    simp [osiiAxisPairGlobalAbsoluteTimeShift,
      osiiAxisPairGlobalTimeDiffShift, hk0, hn, h0n]
  · rw [dif_neg hk0]
    by_cases hkn : k.val = n
    · have hklt : ¬k.val < n := by omega
      simp [osiiAxisPairGlobalAbsoluteTimeShift,
        osiiAxisPairGlobalTimeDiffShift, hkn, hm, hn, hn.ne']
    · by_cases hklt : k.val < n
      · have hprev : k.val - 1 < n := by omega
        simp [osiiAxisPairGlobalAbsoluteTimeShift,
          osiiAxisPairGlobalTimeDiffShift, hk0, hkn, hklt, hprev]
      · have hprev : ¬k.val - 1 < n := by omega
        simp [osiiAxisPairGlobalAbsoluteTimeShift,
          osiiAxisPairGlobalTimeDiffShift, hk0, hkn, hklt, hprev]

/-- The actual chronological absolute-time configuration obtained from
separate block differences. -/
def osiiAxisPairBlockGlobalAbsoluteTimeConfig
    (n m : ℕ) (s t : ℝ) (δ : Fin (n + m) → ℝ) :
    Fin (n + m) → ℝ :=
  osiiAxisPairReflectReverseLeftTimeCLE n m
      ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm δ) +
    osiiAxisPairGlobalAbsoluteTimeShift n m s t

@[simp] theorem osiiAxisPairBlockGlobalAbsoluteTimeConfig_left
    (n m : ℕ) (s t : ℝ) (δ : Fin (n + m) → ℝ) (i : Fin n) :
    osiiAxisPairBlockGlobalAbsoluteTimeConfig n m s t δ
        (Fin.castAdd m i) =
      -(section43ScalarDiffCLE n).symm
          (splitFirst n m δ) (Fin.rev i) + s := by
  simp [osiiAxisPairBlockGlobalAbsoluteTimeConfig,
    osiiAxisPairGlobalAbsoluteTimeShift, splitFirst]

@[simp] theorem osiiAxisPairBlockGlobalAbsoluteTimeConfig_right
    (n m : ℕ) (s t : ℝ) (δ : Fin (n + m) → ℝ) (j : Fin m) :
    osiiAxisPairBlockGlobalAbsoluteTimeConfig n m s t δ
        (Fin.natAdd n j) =
      (section43ScalarDiffCLE m).symm
          (splitLast n m δ) j + (s + t) := by
  simp [osiiAxisPairBlockGlobalAbsoluteTimeConfig,
    osiiAxisPairGlobalAbsoluteTimeShift, splitLast]

/-- Affine two-block-to-global difference-time map. -/
def osiiAxisPairBlockGlobalTimeAffine
    (n m : ℕ) (s t : ℝ) (δ : Fin (n + m) → ℝ) :
    Fin (n + m) → ℝ :=
  osiiAxisPairBlockGlobalTimeCLE n m δ +
    osiiAxisPairGlobalTimeDiffShift n m s t

/-- The affine chart is exactly the global difference chart of the reflected,
reversed, and shifted absolute-time configuration. -/
theorem section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (s t : ℝ) (δ : Fin (n + m) → ℝ) :
    section43ScalarDiffCLE (n + m)
        (osiiAxisPairBlockGlobalAbsoluteTimeConfig n m s t δ) =
      osiiAxisPairBlockGlobalTimeAffine n m s t δ := by
  rw [osiiAxisPairBlockGlobalAbsoluteTimeConfig,
    map_add, section43ScalarDiffCLE_globalAbsoluteTimeShift n m hn hm]
  rfl

/-- Positive left/right block differences become globally strict-positive after
one sufficiently large common shift and a nonnegative right-block separation. -/
theorem osiiAxisPairBlockGlobalTimeAffine_mem_strictPositive
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (s t : ℝ) (ht : 0 ≤ t)
    (δ : Fin (n + m) → ℝ)
    (hδ₁ : ∀ i : Fin n, 0 < splitFirst n m δ i)
    (hδ₂ : ∀ j : Fin m, 0 < splitLast n m δ j)
    (hspan :
      (section43ScalarDiffCLE n).symm (splitFirst n m δ)
          (Fin.rev ⟨0, hn⟩) < s) :
    osiiAxisPairBlockGlobalTimeAffine n m s t δ ∈
      section43TimeStrictPositiveRegion (n + m) := by
  intro k
  rw [← congrFun
    (section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
      n m hn hm s t δ) k]
  rw [section43ScalarDiffCLE_apply]
  by_cases hk0 : k.val = 0
  · rw [dif_pos hk0]
    have hk :
        k = Fin.castAdd m (⟨0, hn⟩ : Fin n) := by
      apply Fin.ext
      simpa using hk0
    rw [hk, osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
    linarith
  · rw [dif_neg hk0]
    by_cases hklt : k.val < n
    · let i : Fin n := ⟨k.val, hklt⟩
      let i' : Fin n := ⟨k.val - 1, by omega⟩
      have hk :
          k = Fin.castAdd m i := by
        apply Fin.ext
        rfl
      rw [hk]
      have hk' :
          (⟨(Fin.castAdd m i).val - 1, by omega⟩ : Fin (n + m)) =
            Fin.castAdd m i' := by
        apply Fin.ext
        simp [i, i']
      rw [hk',
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_left,
        osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
      have hi' : i' < i := by
        exact Fin.mk_lt_mk.mpr (by omega)
      have hrev : Fin.rev i < Fin.rev i' := by
        rw [Fin.rev_lt_iff]
        simpa using hi'
      have hmono :=
        section43ScalarDiffCLE_symm_strictMono hδ₁ hrev
      linarith
    · by_cases hkn : k.val = n
      · let i : Fin n := ⟨n - 1, by omega⟩
        let j : Fin m := ⟨0, hm⟩
        have hk :
            k = Fin.natAdd n j := by
          apply Fin.ext
          simpa [j] using hkn
        rw [hk]
        have hk' :
            (⟨(Fin.natAdd n j).val - 1, by omega⟩ : Fin (n + m)) =
              Fin.castAdd m i := by
          apply Fin.ext
          simp [i, j]
        rw [hk',
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
        have hleft :=
          section43ScalarDiffCLE_symm_pos hδ₁ (Fin.rev i)
        have hright :=
          section43ScalarDiffCLE_symm_pos hδ₂ j
        linarith
      · have hnlt : n < k.val := by omega
        let j : Fin m := ⟨k.val - n, by omega⟩
        let j' : Fin m := ⟨k.val - n - 1, by omega⟩
        have hk :
            k = Fin.natAdd n j := by
          apply Fin.ext
          simp [j]
          omega
        rw [hk]
        have hk' :
            (⟨(Fin.natAdd n j).val - 1, by omega⟩ : Fin (n + m)) =
              Fin.natAdd n j' := by
          apply Fin.ext
          simp [j, j']
          omega
        rw [hk',
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right,
          osiiAxisPairBlockGlobalAbsoluteTimeConfig_right]
        have hj' : j' < j := by
          exact Fin.mk_lt_mk.mpr (by omega)
        have hmono :=
          section43ScalarDiffCLE_symm_strictMono hδ₂ hj'
        linarith

/-- Pull a product of left/right time cutoffs through the affine global
difference chart. -/
noncomputable def osiiAxisPairGlobalTimeCutoff
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ) :
    SchwartzMap (Fin (n + m) → ℝ) ℂ :=
  SCV.translateSchwartz
    (-osiiAxisPairGlobalTimeDiffShift n m s t)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (osiiAxisPairBlockGlobalTimeCLE n m).symm
      (SCV.twoBlockProductSchwartz η₁ η₂))

/-- Compact block tests remain compact after transport to global difference
coordinates and affine translation. -/
theorem osiiAxisPairGlobalTimeCutoff_hasCompactSupport
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₁ : HasCompactSupport (η₁ : (Fin n → ℝ) → ℂ))
    (hη₂ : HasCompactSupport (η₂ : (Fin m → ℝ) → ℂ))
    (s t : ℝ) :
    HasCompactSupport
      (osiiAxisPairGlobalTimeCutoff n m η₁ η₂ s t :
        (Fin (n + m) → ℝ) → ℂ) := by
  let a := osiiAxisPairGlobalTimeDiffShift n m s t
  let product := SCV.twoBlockProductSchwartz η₁ η₂
  have hproduct : HasCompactSupport
      (product : (Fin (n + m) → ℝ) → ℂ) := by
    exact twoBlockProductSchwartz_hasCompactSupport
      n m η₁ η₂ hη₁ hη₂
  have hlinear :=
    hproduct.comp_homeomorph
      (osiiAxisPairBlockGlobalTimeCLE n m).symm.toHomeomorph
  have htranslate :=
    hlinear.comp_homeomorph
      (Homeomorph.addRight (-a))
  change HasCompactSupport
    (fun x : Fin (n + m) → ℝ =>
      product
        ((osiiAxisPairBlockGlobalTimeCLE n m).symm
          (x + (-a))))
  simpa [Function.comp_def, map_add, map_neg] using htranslate

@[simp] theorem osiiAxisPairGlobalTimeCutoff_affine
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ)
    (δ : Fin (n + m) → ℝ) :
    osiiAxisPairGlobalTimeCutoff n m η₁ η₂ s t
        (osiiAxisPairBlockGlobalTimeAffine n m s t δ) =
      η₁ (splitFirst n m δ) * η₂ (splitLast n m δ) := by
  simp [osiiAxisPairGlobalTimeCutoff,
    osiiAxisPairBlockGlobalTimeAffine,
    SCV.translateSchwartz_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    twoBlockProductSchwartz_apply_split, add_assoc]

/-- The transported two-block cutoff has global strict-positive support once
the common shift dominates the reflected left endpoint. -/
theorem osiiAxisPairGlobalTimeCutoff_tsupport_subset_strictPositive
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s) :
    tsupport (osiiAxisPairGlobalTimeCutoff n m η₁ η₂ s t :
        (Fin (n + m) → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion (n + m) := by
  intro x hx
  let a := osiiAxisPairGlobalTimeDiffShift n m s t
  let e := osiiAxisPairBlockGlobalTimeCLE n m
  let product := SCV.twoBlockProductSchwartz η₁ η₂
  have hshift : Continuous (fun y : Fin (n + m) → ℝ => y + (-a)) :=
    continuous_id.add continuous_const
  have hxbase :
      x + (-a) ∈ tsupport
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm product :
          (Fin (n + m) → ℝ) → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm product :
          (Fin (n + m) → ℝ) → ℂ)
        hshift
    apply hpre
    change x ∈ tsupport (fun y : Fin (n + m) → ℝ =>
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm product) (y + (-a))) at hx
    exact hx
  let δ := e.symm (x + (-a))
  have hδ_product :
      δ ∈ tsupport (product : (Fin (n + m) → ℝ) → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        (product : (Fin (n + m) → ℝ) → ℂ) e.symm.continuous
    apply hpre
    simpa [δ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hxbase
  have hparts :=
    twoBlockProductSchwartz_tsupport_subset n m η₁ η₂ hδ_product
  have hδ_pos :=
    osiiAxisPairBlockGlobalTimeAffine_mem_strictPositive
      n m hn hm s t ht δ (hη₁ hparts.1) (hη₂ hparts.2)
        (hspan _ hparts.1)
  have hx_affine :
      x = osiiAxisPairBlockGlobalTimeAffine n m s t δ := by
    simp [δ, e, a, osiiAxisPairBlockGlobalTimeAffine, add_assoc]
  rw [hx_affine]
  exact hδ_pos

/-- Compactness of the left time cutoff supplies a common translation larger
than every reflected left endpoint on its support. -/
theorem exists_osiiAxisPairCommonShift_gt_leftTimeSpan
    {n : ℕ}
    (hn : 0 < n)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : HasCompactSupport (η : (Fin n → ℝ) → ℂ)) :
    ∃ s : ℝ, 0 < s ∧
      ∀ δ ∈ tsupport (η : (Fin n → ℝ) → ℂ),
        (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s := by
  have hK : IsCompact (tsupport (η : (Fin n → ℝ) → ℂ)) := by
    simpa [HasCompactSupport] using hη
  have hendpoint : Continuous (fun δ : Fin n → ℝ =>
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩)) :=
    (continuous_apply (Fin.rev ⟨0, hn⟩)).comp
      (section43ScalarDiffCLE n).symm.continuous
  by_cases hne : (tsupport (η : (Fin n → ℝ) → ℂ)).Nonempty
  · obtain ⟨δ₀, hδ₀, hδ₀_max⟩ :=
      hK.exists_isMaxOn hne hendpoint.continuousOn
    let endpoint₀ :=
      (section43ScalarDiffCLE n).symm δ₀ (Fin.rev ⟨0, hn⟩)
    refine ⟨max endpoint₀ 0 + 1, ?_, ?_⟩
    · have hnonneg : 0 ≤ max endpoint₀ 0 := le_max_right _ _
      linarith
    · intro δ hδ
      have hle :
          (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) ≤
            endpoint₀ := hδ₀_max hδ
      have hmax : endpoint₀ ≤ max endpoint₀ 0 := le_max_left _ _
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro δ hδ
    exact False.elim (hne ⟨δ, hδ⟩)

end OSReconstruction
