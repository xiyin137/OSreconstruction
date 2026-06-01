import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanAdjacentNormalForm

/-!
# Reduced Adjacent Frozen-Spectator Normal Form

The absolute adjacent normal form records that an adjacent transposition fixes
the pair center and spectator-relative variables, and negates the selected
difference.  The reduced theorem-2 route quotients out global translations, so
the center coordinate is discarded.  This file records that quotient-level
normal form for the induced reduced permutation.
-/

open scoped Classical NNReal

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

namespace AdjacentNormal

omit [NeZero d] in
/-- Translation of every absolute point shifts the pair center by the same
amount. -/
theorem pairCenter_translate_eq
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n)
    (c : SpacetimeDim d) :
    pairCenter (d := d) i j (fun k μ => x k μ + c μ) =
      fun μ => pairCenter (d := d) i j x μ + c μ := by
  ext μ
  simp [pairCenter, div_eq_mul_inv]
  ring

omit [NeZero d] in
/-- Translation of every absolute point leaves the selected pair difference
unchanged. -/
theorem pairDiff_translate_eq
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n)
    (c : SpacetimeDim d) :
    pairDiff (d := d) i j (fun k μ => x k μ + c μ) =
      pairDiff (d := d) i j x := by
  ext μ
  simp [pairDiff]

omit [NeZero d] in
/-- Translation of every absolute point leaves every spectator-relative
coordinate unchanged. -/
theorem spectatorRel_translate_eq
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n)
    (c : SpacetimeDim d) (k : SpectatorIndex n i j) :
    spectatorRel (d := d) i j (fun a μ => x a μ + c μ) k =
      spectatorRel (d := d) i j x k := by
  ext μ
  simp [spectatorRel, pairCenter_translate_eq (d := d) i j x c]

/-- The reduced frozen-spectator normal coordinates: selected difference and
all spectator positions relative to the selected pair center.  The absolute
center coordinate is omitted because reduced coordinates quotient out uniform
translations. -/
abbrev ReducedSpace
    (d m : ℕ) (i j : Fin (m + 1)) : Type :=
  SpacetimeDim d × (SpectatorIndex (m + 1) i j → SpacetimeDim d)

omit [NeZero d] in
/-- Project absolute adjacent normal coordinates to the reduced quotient
coordinates. -/
def quotientCoord
    {m : ℕ} (i j : Fin (m + 1))
    (p : Space d (m + 1) i j) :
    ReducedSpace d m i j :=
  (p.2.1, p.2.2)

omit [NeZero d] in
/-- Translation of every absolute point does not affect the reduced adjacent
normal coordinates. -/
theorem quotientCoord_coord_translate_eq
    {m : ℕ} (i j : Fin (m + 1))
    (x : NPointDomain d (m + 1)) (c : SpacetimeDim d) :
    quotientCoord (d := d) i j
        (coord (d := d) i j (fun k μ => x k μ + c μ)) =
      quotientCoord (d := d) i j (coord (d := d) i j x) := by
  apply Prod.ext
  · exact pairDiff_translate_eq (d := d) i j x c
  · funext k
    exact spectatorRel_translate_eq (d := d) i j x c k

omit [NeZero d] in
/-- The reduced adjacent sign flip: negate the selected difference and leave
all frozen spectators fixed. -/
def reducedSignFlip
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) :
    ReducedSpace d m i j :=
  (-p.1, p.2)

omit [NeZero d] in
/-- Projecting the absolute sign flip gives the reduced sign flip. -/
theorem quotientCoord_signFlip
    {m : ℕ} (i j : Fin (m + 1))
    (p : Space d (m + 1) i j) :
    quotientCoord (d := d) i j (signFlip (d := d) i j p) =
      reducedSignFlip (d := d) i j
        (quotientCoord (d := d) i j p) := by
  rfl

/-- Zero-basepoint section of reduced real difference coordinates. -/
def reducedSection
    (m : ℕ) (ξ : NPointDomain d m) : NPointDomain d (m + 1) :=
  (BHW.realDiffCoordCLE (m + 1) d).symm
    (BHW.prependBasepointReal d m 0 ξ)

/-- Reduced frozen-spectator normal coordinates, obtained by taking the
zero-basepoint absolute section and discarding the absolute pair center. -/
def reducedCoord
    {m : ℕ} (i j : Fin (m + 1))
    (ξ : NPointDomain d m) :
    ReducedSpace d m i j :=
  quotientCoord (d := d) i j
    (coord (d := d) i j (reducedSection (d := d) m ξ))

omit [NeZero d] in
/-- Reinsert the reduced frozen-spectator variables as absolute normal
coordinates with zero pair center, then return to reduced successive
differences. -/
def reducedCoordInv
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (p : ReducedSpace d m i j) : NPointDomain d m :=
  BHW.reducedDiffMapReal (m + 1) d
    (coordInv (d := d) i j hij ((0 : SpacetimeDim d), p))

omit [NeZero d] in
/-- Setting the absolute pair center to zero reconstructs the original
absolute configuration translated by the negative of its pair center. -/
theorem coordInv_zero_quotientCoord_eq_sub_pairCenter
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (x : NPointDomain d (m + 1)) :
    coordInv (d := d) i j hij
        ((0 : SpacetimeDim d),
          quotientCoord (d := d) i j (coord (d := d) i j x)) =
      fun k μ => x k μ - pairCenter (d := d) i j x μ := by
  ext k μ
  by_cases hki : k = i
  · subst k
    simp [coordInv, quotientCoord, coord, pairCenter, pairDiff,
      div_eq_mul_inv]
    ring
  · by_cases hkj : k = j
    · subst k
      simp [coordInv, quotientCoord, coord, pairCenter, pairDiff,
        hki, div_eq_mul_inv]
      ring
    · simp [coordInv, quotientCoord, coord, spectatorRel, hki, hkj]

omit [NeZero d] in
/-- Reconstructing the zero-basepoint section from the reduced differences of
an absolute configuration gives that configuration translated so that its
zeroth point is at the origin. -/
theorem reducedSection_reducedDiffMapReal_eq_sub_basepoint
    (m : ℕ) (x : NPointDomain d (m + 1)) :
    reducedSection (d := d) m
        (BHW.reducedDiffMapReal (m + 1) d x) =
      fun k μ => x k μ - x 0 μ := by
  let y : NPointDomain d (m + 1) := fun k μ => x k μ - x 0 μ
  have hy :
      BHW.realDiffCoordCLE (m + 1) d y =
        BHW.prependBasepointReal d m 0
          (BHW.reducedDiffMapReal (m + 1) d x) := by
    ext k μ
    by_cases hk : k.val = 0
    · have hk0 : k = 0 := Fin.ext hk
      subst k
      simp [BHW.realDiffCoordCLE_apply, BHW.prependBasepointReal, y]
    · simp [BHW.realDiffCoordCLE_apply, BHW.prependBasepointReal, y, hk]
      change
        x k μ - x ⟨k.val - 1, by omega⟩ μ =
          x ⟨(⟨k.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ μ -
            x ⟨(⟨k.val - 1, by omega⟩ : Fin m).val, by omega⟩ μ
      congr 2
      · ext
        simp
        omega
  change
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0
          (BHW.reducedDiffMapReal (m + 1) d x)) = y
  rw [← hy]
  exact (BHW.realDiffCoordCLE (m + 1) d).symm_apply_apply y

omit [NeZero d] in
/-- Reduced normal coordinates followed by their inverse recover the original
reduced differences. -/
theorem reducedCoordInv_left
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (ξ : NPointDomain d m) :
    reducedCoordInv (d := d) i j hij
        (reducedCoord (d := d) i j ξ) = ξ := by
  let x : NPointDomain d (m + 1) := reducedSection (d := d) m ξ
  have hcoord :
      coordInv (d := d) i j hij
          ((0 : SpacetimeDim d),
            quotientCoord (d := d) i j (coord (d := d) i j x)) =
        fun k μ => x k μ - pairCenter (d := d) i j x μ :=
    coordInv_zero_quotientCoord_eq_sub_pairCenter (d := d) i j hij x
  have hred_translate :
      BHW.reducedDiffMapReal (m + 1) d
          (fun k μ => x k μ - pairCenter (d := d) i j x μ) =
        BHW.reducedDiffMapReal (m + 1) d x := by
    let c : SpacetimeDim d := fun μ => -pairCenter (d := d) i j x μ
    have h :=
      BHW.reducedDiffMapReal_translate_uniform_eq (m + 1) d x c
    simpa [c, sub_eq_add_neg] using h
  have hsection :
      BHW.reducedDiffMapReal (m + 1) d x = ξ := by
    simpa [x, reducedSection] using
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) (m := m) (0 : SpacetimeDim d) ξ
  change
    BHW.reducedDiffMapReal (m + 1) d
        (coordInv (d := d) i j hij
          ((0 : SpacetimeDim d),
            quotientCoord (d := d) i j (coord (d := d) i j x))) = ξ
  rw [hcoord, hred_translate, hsection]

omit [NeZero d] in
/-- The inverse reduced normal chart followed by reduced normal coordinates is
the identity. -/
theorem reducedCoordInv_right
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (p : ReducedSpace d m i j) :
    reducedCoord (d := d) i j
        (reducedCoordInv (d := d) i j hij p) = p := by
  let x : NPointDomain d (m + 1) :=
    coordInv (d := d) i j hij ((0 : SpacetimeDim d), p)
  have hsection :
      reducedSection (d := d) m
          (BHW.reducedDiffMapReal (m + 1) d x) =
        fun k μ => x k μ - x 0 μ :=
    reducedSection_reducedDiffMapReal_eq_sub_basepoint (d := d) m x
  have hquot_translate :
      quotientCoord (d := d) i j
          (coord (d := d) i j (fun k μ => x k μ - x 0 μ)) =
        quotientCoord (d := d) i j (coord (d := d) i j x) := by
    let c : SpacetimeDim d := fun μ => -x 0 μ
    have h :=
      quotientCoord_coord_translate_eq (d := d) i j x c
    simpa [c, sub_eq_add_neg] using h
  have hcoord :
      coord (d := d) i j x = ((0 : SpacetimeDim d), p) :=
    coordInv_right (d := d) i j hij ((0 : SpacetimeDim d), p)
  calc
    reducedCoord (d := d) i j (reducedCoordInv (d := d) i j hij p)
        =
      quotientCoord (d := d) i j
        (coord (d := d) i j
          (reducedSection (d := d) m
            (BHW.reducedDiffMapReal (m + 1) d x))) := rfl
    _ =
      quotientCoord (d := d) i j
        (coord (d := d) i j (fun k μ => x k μ - x 0 μ)) := by
        rw [hsection]
    _ =
      quotientCoord (d := d) i j (coord (d := d) i j x) :=
        hquot_translate
    _ = quotientCoord (d := d) i j ((0 : SpacetimeDim d), p) := by
        rw [hcoord]
    _ = p := rfl

omit [NeZero d] in
/-- The zero-basepoint reduced section is additive in the reduced
successive-difference variables. -/
theorem reducedSection_add
    (m : ℕ) (ξ η : NPointDomain d m) :
    reducedSection (d := d) m (ξ + η) =
      reducedSection (d := d) m ξ + reducedSection (d := d) m η := by
  have hpre :
      BHW.prependBasepointReal d m 0 (ξ + η) =
        BHW.prependBasepointReal d m 0 ξ +
          BHW.prependBasepointReal d m 0 η := by
    ext k μ
    by_cases hk : k.val = 0
    · simp [BHW.prependBasepointReal, hk]
    · simp [BHW.prependBasepointReal, hk, Pi.add_apply]
  change
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 (ξ + η)) =
      (BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m 0 ξ) +
        (BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m 0 η)
  rw [hpre]
  exact (BHW.realDiffCoordCLE (m + 1) d).symm.map_add
    (BHW.prependBasepointReal d m 0 ξ)
    (BHW.prependBasepointReal d m 0 η)

omit [NeZero d] in
/-- The zero-basepoint reduced section is real homogeneous in the reduced
successive-difference variables. -/
theorem reducedSection_smul
    (m : ℕ) (a : ℝ) (ξ : NPointDomain d m) :
    reducedSection (d := d) m (a • ξ) =
      a • reducedSection (d := d) m ξ := by
  have hpre :
      BHW.prependBasepointReal d m 0 (a • ξ) =
        a • BHW.prependBasepointReal d m 0 ξ := by
    ext k μ
    by_cases hk : k.val = 0
    · simp [BHW.prependBasepointReal, hk]
    · simp [BHW.prependBasepointReal, hk, Pi.smul_apply]
  change
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 (a • ξ)) =
      a •
        (BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m 0 ξ)
  rw [hpre]
  exact (BHW.realDiffCoordCLE (m + 1) d).symm.map_smul a
    (BHW.prependBasepointReal d m 0 ξ)

omit [NeZero d] in
/-- The first reduced normal coordinate is the selected reduced pair
difference. -/
theorem reducedCoord_fst_eq_reducedPairDiff
    {m : ℕ} (i j : Fin (m + 1)) (ξ : NPointDomain d m) :
    (reducedCoord (d := d) i j ξ).1 =
      reducedPairDiff (d := d) m i j ξ := by
  rfl

omit [NeZero d] in
/-- The reduced frozen-spectator coordinate map is a real linear
equivalence.  This is the quotient-level chart used to transport compact
Schwartz tests into the one selected-difference normal form. -/
noncomputable def reducedCoordLinearEquiv
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) :
    NPointDomain d m ≃ₗ[ℝ] ReducedSpace d m i j where
  toFun := reducedCoord (d := d) i j
  invFun := reducedCoordInv (d := d) i j hij
  left_inv := reducedCoordInv_left (d := d) i j hij
  right_inv := reducedCoordInv_right (d := d) i j hij
  map_add' := by
    intro ξ η
    have hsec :
        reducedSection (d := d) m (ξ + η) =
          reducedSection (d := d) m ξ +
            reducedSection (d := d) m η :=
      reducedSection_add (d := d) m ξ η
    change
      quotientCoord (d := d) i j
          (coord (d := d) i j
            (reducedSection (d := d) m (ξ + η))) =
        quotientCoord (d := d) i j
            (coord (d := d) i j (reducedSection (d := d) m ξ)) +
          quotientCoord (d := d) i j
            (coord (d := d) i j (reducedSection (d := d) m η))
    rw [hsec]
    apply Prod.ext
    · ext μ
      simp [quotientCoord, coord, pairDiff, Pi.add_apply]
      ring
    · funext k
      ext μ
      simp [quotientCoord, coord, spectatorRel, pairCenter, Pi.add_apply,
        div_eq_mul_inv]
      ring
  map_smul' := by
    intro a ξ
    have hsec :
        reducedSection (d := d) m (a • ξ) =
          a • reducedSection (d := d) m ξ :=
      reducedSection_smul (d := d) m a ξ
    change
      quotientCoord (d := d) i j
          (coord (d := d) i j (reducedSection (d := d) m (a • ξ))) =
        a • quotientCoord (d := d) i j
          (coord (d := d) i j (reducedSection (d := d) m ξ))
    rw [hsec]
    apply Prod.ext
    · ext μ
      simp [quotientCoord, coord, pairDiff, Pi.smul_apply]
      ring
    · funext k
      ext μ
      simp [quotientCoord, coord, spectatorRel, pairCenter, Pi.smul_apply,
        div_eq_mul_inv]
      ring

omit [NeZero d] in
/-- Continuous-linear version of the reduced frozen-spectator coordinates. -/
noncomputable def reducedCoordCLE
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j) :
    NPointDomain d m ≃L[ℝ] ReducedSpace d m i j :=
  (reducedCoordLinearEquiv (d := d) i j hij).toContinuousLinearEquiv

omit [NeZero d] in
/-- The selected spacelike collar in reduced frozen-spectator coordinates. -/
def reducedSelectedSpacelike
    {m : ℕ} (i j : Fin (m + 1)) :
    Set (ReducedSpace d m i j) :=
  {p | MinkowskiSpace.IsSpacelike d p.1}

omit [NeZero d] in
/-- The reduced normal chart identifies the adjacent reduced spacelike edge
with the selected spacelike collar in normal coordinates. -/
theorem reducedCoord_mem_reducedSelectedSpacelike_iff
    {m : ℕ} (i j : Fin (m + 1)) (ξ : NPointDomain d m) :
    reducedCoord (d := d) i j ξ ∈
        reducedSelectedSpacelike (d := d) i j ↔
      ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j := by
  change MinkowskiSpace.IsSpacelike d
      ((reducedCoord (d := d) i j ξ).1) ↔
    MinkowskiSpace.IsSpacelike d
      (reducedPairDiff (d := d) m i j ξ)
  rw [reducedCoord_fst_eq_reducedPairDiff (d := d) i j ξ]

omit [NeZero d] in
/-- The inverse reduced normal chart carries the selected spacelike collar back
to the adjacent reduced spacelike edge. -/
theorem reducedCoordInv_mem_reducedSpacelikeSwapEdge_iff
    {m : ℕ} (i j : Fin (m + 1)) (hij : i ≠ j)
    (p : ReducedSpace d m i j) :
    reducedCoordInv (d := d) i j hij p ∈
        reducedSpacelikeSwapEdge (d := d) m i j ↔
      p ∈ reducedSelectedSpacelike (d := d) i j := by
  have h :=
    reducedCoord_mem_reducedSelectedSpacelike_iff
      (d := d) i j (reducedCoordInv (d := d) i j hij p)
  simpa [reducedCoordInv_right (d := d) i j hij p] using h.symm

omit [NeZero d] in
/-- The reduced selected spacelike collar is open in reduced normal
coordinates. -/
theorem isOpen_reducedSelectedSpacelike
    {m : ℕ} (i j : Fin (m + 1)) :
    IsOpen (reducedSelectedSpacelike (d := d) i j) := by
  have hquad : Continuous
      (fun p : ReducedSpace d m i j =>
        MinkowskiSpace.minkowskiNormSq d p.1) := by
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    exact continuous_finset_sum _ fun μ _ =>
      (continuous_const.mul ((continuous_apply μ).comp continuous_fst)).mul
        ((continuous_apply μ).comp continuous_fst)
  simpa [reducedSelectedSpacelike, MinkowskiSpace.IsSpacelike] using
    hquad.isOpen_preimage _ isOpen_Ioi

omit [NeZero d] in
/-- The reduced adjacent sign flip is a real linear involution. -/
noncomputable def reducedSignFlipLinearEquiv
    {m : ℕ} (i j : Fin (m + 1)) :
    ReducedSpace d m i j ≃ₗ[ℝ] ReducedSpace d m i j where
  toFun := reducedSignFlip (d := d) i j
  invFun := reducedSignFlip (d := d) i j
  left_inv := by
    intro p
    ext <;> simp [reducedSignFlip]
  right_inv := by
    intro p
    ext <;> simp [reducedSignFlip]
  map_add' := by
    intro p q
    apply Prod.ext
    · ext μ
      simp [reducedSignFlip]
      ring
    · funext k
      ext μ
      simp [reducedSignFlip]
  map_smul' := by
    intro a p
    apply Prod.ext
    · ext μ
      simp [reducedSignFlip]
    · funext k
      ext μ
      simp [reducedSignFlip]

omit [NeZero d] in
/-- Continuous-linear version of the reduced normal-form sign flip. -/
noncomputable def reducedSignFlipCLE
    {m : ℕ} (i j : Fin (m + 1)) :
    ReducedSpace d m i j ≃L[ℝ] ReducedSpace d m i j :=
  { toLinearEquiv := reducedSignFlipLinearEquiv (d := d) i j
    continuous_toFun := by
      change Continuous
        (fun p : ReducedSpace d m i j =>
          reducedSignFlip (d := d) i j p)
      have hv : Continuous (fun p : ReducedSpace d m i j => p.1) :=
        continuous_fst
      have hs : Continuous (fun p : ReducedSpace d m i j => p.2) :=
        continuous_snd
      simpa [reducedSignFlip] using hv.neg.prodMk hs
    continuous_invFun := by
      change Continuous
        (fun p : ReducedSpace d m i j =>
          reducedSignFlip (d := d) i j p)
      have hv : Continuous (fun p : ReducedSpace d m i j => p.1) :=
        continuous_fst
      have hs : Continuous (fun p : ReducedSpace d m i j => p.2) :=
        continuous_snd
      simpa [reducedSignFlip] using hv.neg.prodMk hs }

/-- The reduced selected spacelike collar is invariant under the reduced
normal-form sign flip. -/
theorem reducedSelectedSpacelike_signFlip_iff
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) :
    reducedSignFlip (d := d) i j p ∈
        reducedSelectedSpacelike (d := d) i j ↔
      p ∈ reducedSelectedSpacelike (d := d) i j := by
  change MinkowskiSpace.IsSpacelike d (-p.1) ↔
    MinkowskiSpace.IsSpacelike d p.1
  exact minkowski_isSpacelike_neg_iff (d := d) p.1

/-- Every selected reduced normal spacelike point has an open collar, invariant
under the reduced adjacent sign flip, still contained in the selected
spacelike edge. -/
theorem exists_reducedSelectedSpacelike_signFlip_invariant_open_nhds
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j)
    (hp : p ∈ reducedSelectedSpacelike (d := d) i j) :
    ∃ V : Set (ReducedSpace d m i j),
      IsOpen V ∧ p ∈ V ∧
        V ⊆ reducedSelectedSpacelike (d := d) i j ∧
        (∀ q ∈ V, reducedSignFlip (d := d) i j q ∈ V) := by
  refine
    ⟨reducedSelectedSpacelike (d := d) i j,
      isOpen_reducedSelectedSpacelike (d := d) i j, hp, subset_rfl, ?_⟩
  intro q hq
  exact (reducedSelectedSpacelike_signFlip_iff (d := d) i j q).2 hq

omit [NeZero d] in
/-- The zero-basepoint section of an induced reduced permutation is the
absolute permuted zero-basepoint section, translated back to basepoint zero. -/
theorem reducedSection_realPerm_eq_sub_basepoint
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) :
    reducedSection (d := d) m
        (realPermOnReducedDiff (d := d) m σ ξ) =
      fun k μ =>
        reducedSection (d := d) m ξ (σ k) μ -
          reducedSection (d := d) m ξ (σ 0) μ := by
  let x : NPointDomain d (m + 1) := reducedSection (d := d) m ξ
  have hperm :
      BHW.reducedDiffMapReal (m + 1) d (fun k => x (σ k)) =
        realPermOnReducedDiff (d := d) m σ ξ := by
    simpa [x, reducedSection] using
      reducedDiffMapReal_permute_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) m σ (0 : SpacetimeDim d) ξ
  calc
    reducedSection (d := d) m
        (realPermOnReducedDiff (d := d) m σ ξ)
        =
      reducedSection (d := d) m
        (BHW.reducedDiffMapReal (m + 1) d (fun k => x (σ k))) := by
        rw [hperm]
    _ = fun k μ => x (σ k) μ - x (σ 0) μ := by
        exact reducedSection_reducedDiffMapReal_eq_sub_basepoint
          (d := d) m (fun k => x (σ k))
    _ =
      fun k μ =>
        reducedSection (d := d) m ξ (σ k) μ -
          reducedSection (d := d) m ξ (σ 0) μ := rfl

omit [NeZero d] in
/-- In reduced frozen-spectator coordinates, the induced adjacent reduced
permutation is exactly the sign flip of the selected spacelike difference. -/
theorem reducedCoord_realPerm_adjacentSwap_eq_reducedSignFlip
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    reducedCoord (d := d) i ⟨i.val + 1, hi⟩
        (realPermOnReducedDiff (d := d) m
          (Equiv.swap i ⟨i.val + 1, hi⟩) ξ) =
      reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩
        (reducedCoord (d := d) i ⟨i.val + 1, hi⟩ ξ) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let x : NPointDomain d (m + 1) := reducedSection (d := d) m ξ
  have hsection :
      reducedSection (d := d) m (realPermOnReducedDiff (d := d) m τ ξ) =
        fun k μ => x (τ k) μ - x (τ 0) μ := by
    simpa [x, τ] using
      reducedSection_realPerm_eq_sub_basepoint (d := d) m τ ξ
  have htranslate :
      quotientCoord (d := d) i j
          (coord (d := d) i j
            (fun k μ => x (τ k) μ - x (τ 0) μ)) =
        quotientCoord (d := d) i j
          (coord (d := d) i j (fun k => x (τ k))) := by
    let c : SpacetimeDim d := fun μ => -x (τ 0) μ
    have h :=
      quotientCoord_coord_translate_eq
        (d := d) i j (fun k => x (τ k)) c
    simpa [c, sub_eq_add_neg] using h
  have hswap :
      quotientCoord (d := d) i j
          (coord (d := d) i j (fun k => x (τ k))) =
        quotientCoord (d := d) i j
          (signFlip (d := d) i j (coord (d := d) i j x)) := by
    simpa [j, τ] using
      congrArg (quotientCoord (d := d) i j)
        (coord_swap_eq_signFlip (d := d) i hi x)
  calc
    reducedCoord (d := d) i j
        (realPermOnReducedDiff (d := d) m τ ξ)
        =
      quotientCoord (d := d) i j
        (coord (d := d) i j
          (reducedSection (d := d) m
            (realPermOnReducedDiff (d := d) m τ ξ))) := rfl
    _ =
      quotientCoord (d := d) i j
        (coord (d := d) i j
          (fun k μ => x (τ k) μ - x (τ 0) μ)) := by rw [hsection]
    _ =
      quotientCoord (d := d) i j
        (coord (d := d) i j (fun k => x (τ k))) := htranslate
    _ =
      quotientCoord (d := d) i j
        (signFlip (d := d) i j (coord (d := d) i j x)) := hswap
    _ =
      reducedSignFlip (d := d) i j
        (quotientCoord (d := d) i j (coord (d := d) i j x)) := by
        rw [quotientCoord_signFlip]
    _ =
      reducedSignFlip (d := d) i j (reducedCoord (d := d) i j ξ) := rfl

omit [NeZero d] in
/-- The adjacent successor label is distinct from the selected label. -/
theorem reducedAdjacent_succ_ne
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro h
  have hv : i.val = i.val + 1 := by
    simpa using congrArg Fin.val h
  omega

/-- Every adjacent reduced spacelike edge point has an open collar in reduced
successive-difference coordinates, invariant under the induced adjacent real
permutation and contained in the adjacent spacelike edge.

This is the reduced-coordinate form of the local support collar used by the
Ruelle/Jost partition-of-unity step.  The proof transports the normal-form
sign-flip collar through the reduced frozen-spectator chart. -/
theorem exists_reducedSpacelikeSwapEdge_adjacent_realPerm_invariant_open_nhds
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m)
    (hξ : ξ ∈ reducedSpacelikeSwapEdge
      (d := d) m i ⟨i.val + 1, hi⟩) :
    ∃ V : Set (NPointDomain d m),
      IsOpen V ∧ ξ ∈ V ∧
        V ⊆ reducedSpacelikeSwapEdge
          (d := d) m i ⟨i.val + 1, hi⟩ ∧
        (∀ η ∈ V,
          realPermOnReducedDiff (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩) η ∈ V) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := reducedAdjacent_succ_ne i hi
  let p : ReducedSpace d m i j := reducedCoord (d := d) i j ξ
  have hp : p ∈ reducedSelectedSpacelike (d := d) i j := by
    simpa [p, j] using
      (reducedCoord_mem_reducedSelectedSpacelike_iff
        (d := d) i j ξ).2 hξ
  obtain ⟨Vn, hVn_open, hpVn, hVn_edge, hVn_flip⟩ :=
    exists_reducedSelectedSpacelike_signFlip_invariant_open_nhds
      (d := d) i j p hp
  let V : Set (NPointDomain d m) :=
    (reducedCoord (d := d) i j) ⁻¹' Vn
  have hV_open : IsOpen V := by
    have hcoord_cont :
        Continuous (reducedCoord (d := d) i j :
          NPointDomain d m → ReducedSpace d m i j) :=
      (reducedCoordCLE (d := d) i j hij).continuous
    exact hVn_open.preimage hcoord_cont
  refine ⟨V, hV_open, ?_, ?_, ?_⟩
  · simpa [V, p]
  · intro η hη
    have hnormal :
        reducedCoord (d := d) i j η ∈
          reducedSelectedSpacelike (d := d) i j :=
      hVn_edge hη
    simpa [j] using
      (reducedCoord_mem_reducedSelectedSpacelike_iff
        (d := d) i j η).1 hnormal
  · intro η hη
    change
      reducedCoord (d := d) i j
          (realPermOnReducedDiff (d := d) m (Equiv.swap i j) η) ∈ Vn
    have hflip :
        reducedSignFlip (d := d) i j
            (reducedCoord (d := d) i j η) ∈ Vn :=
      hVn_flip (reducedCoord (d := d) i j η) hη
    rw [reducedCoord_realPerm_adjacentSwap_eq_reducedSignFlip
      (d := d) i hi η]
    exact hflip

omit [NeZero d] in
/-- The inverse reduced normal chart intertwines the reduced sign flip with the
induced adjacent reduced real permutation. -/
theorem reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)
      =
    realPermOnReducedDiff (d := d) m
      (Equiv.swap i ⟨i.val + 1, hi⟩)
      (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi) p) := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := reducedAdjacent_succ_ne i hi
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let ξ : NPointDomain d m := reducedCoordInv (d := d) i j hij p
  have hcoord :
      reducedCoord (d := d) i j
          (realPermOnReducedDiff (d := d) m τ ξ) =
        reducedSignFlip (d := d) i j p := by
    have h :=
      reducedCoord_realPerm_adjacentSwap_eq_reducedSignFlip
        (d := d) i hi ξ
    simpa [j, τ, ξ, hij, reducedCoordInv_right (d := d) i j hij p] using h
  have hcongr :=
    congrArg (reducedCoordInv (d := d) i j hij) hcoord
  have hleft :
      reducedCoordInv (d := d) i j hij
          (reducedCoord (d := d) i j
            (realPermOnReducedDiff (d := d) m τ ξ)) =
        realPermOnReducedDiff (d := d) m τ ξ :=
    reducedCoordInv_left (d := d) i j hij
      (realPermOnReducedDiff (d := d) m τ ξ)
  simpa [j, τ, hij, ξ] using hcongr.symm.trans hleft

omit [NeZero d] in
/-- Pulling a reduced Schwartz test into reduced frozen-spectator coordinates
converts the adjacent reduced permutation into the normal sign flip. -/
theorem reducedSchwartz_signFlip_pullback_apply
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (p : ReducedSpace d m i ⟨i.val + 1, hi⟩) :
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (reducedSignFlipCLE (d := d) i ⟨i.val + 1, hi⟩))
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi)).symm) φ)) p =
      φ (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi) p)) := by
  change
    φ (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
        (reducedAdjacent_succ_ne i hi)
        (reducedSignFlip (d := d) i ⟨i.val + 1, hi⟩ p)) =
      φ (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (reducedCoordInv (d := d) i ⟨i.val + 1, hi⟩
          (reducedAdjacent_succ_ne i hi) p))
  rw [reducedCoordInv_reducedSignFlip_eq_realPerm_adjacentSwap
    (d := d) i hi p]

omit [NeZero d] in
/-- A reduced test supported on the selected adjacent spacelike edge pulls back
to a reduced normal-coordinate test supported where the selected normal
difference is spacelike. -/
theorem reducedSchwartz_support_subset_reducedSelectedSpacelike
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Function.support
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (reducedCoordCLE (d := d) i ⟨i.val + 1, hi⟩
            (reducedAdjacent_succ_ne i hi)).symm) φ) :
          ReducedSpace d m i ⟨i.val + 1, hi⟩ → ℂ)
      ⊆ reducedSelectedSpacelike (d := d) i ⟨i.val + 1, hi⟩ := by
  intro p hp
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := reducedAdjacent_succ_ne i hi
  let ξ : NPointDomain d m := reducedCoordInv (d := d) i j hij p
  have hφξ : φ.toFun ξ ≠ 0 := by
    change
      (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (reducedCoordCLE (d := d) i j hij).symm) φ) p) ≠ 0
    simpa [ξ, j, hij, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hp
  have hξ_edge :
      ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j :=
    hφ_support (by simpa [ξ] using hφξ)
  have hξ_sp :
      MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ) := by
    simpa [reducedSpacelikeSwapEdge] using hξ_edge
  have hfirst :
      reducedPairDiff (d := d) m i j ξ = p.1 := by
    have hright :=
      reducedCoordInv_right (d := d) i j hij p
    simpa [ξ, reducedCoord_fst_eq_reducedPairDiff (d := d) i j ξ] using
      congrArg Prod.fst hright
  change MinkowskiSpace.IsSpacelike d p.1
  simpa [hfirst] using hξ_sp

omit [NeZero d] in
/-- Flatten the spectator block of reduced adjacent normal coordinates into
ordinary finite real coordinates. -/
noncomputable def reducedSpectatorFlattenCLE
    {m : ℕ} (i j : Fin (m + 1)) :
    (SpectatorIndex (m + 1) i j → SpacetimeDim d) ≃L[ℝ]
      (Fin (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin (Fintype.card (SpectatorIndex (m + 1) i j)) =>
        SpacetimeDim d)
      (Fintype.equivFin (SpectatorIndex (m + 1) i j))).trans
    (SCV.realBlockFlattenCLE
      (Fintype.card (SpectatorIndex (m + 1) i j)) (d + 1))

omit [NeZero d] in
/-- Flatten reduced adjacent normal coordinates into the standard
`Fin q → ℝ` chart used by the local SCV EOW theorems.  The head block is the
selected adjacent difference; the tail block consists of the frozen spectator
coordinates. -/
noncomputable def reducedNormalFlattenCLE
    {m : ℕ} (i j : Fin (m + 1)) :
    ReducedSpace d m i j ≃L[ℝ]
      (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :=
  (ContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (SpacetimeDim d))
      (reducedSpectatorFlattenCLE (d := d) i j)).trans
    (SCV.finAppendCLE (d + 1)
      (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)))

omit [NeZero d] in
@[simp]
theorem reducedNormalFlattenCLE_apply_head
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) (μ : Fin (d + 1)) :
    reducedNormalFlattenCLE (d := d) i j p
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) =
      p.1 μ := by
  simp [reducedNormalFlattenCLE]

omit [NeZero d] in
@[simp]
theorem reducedNormalFlattenCLE_apply_tail
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j)
    (k : SpectatorIndex (m + 1) i j) (μ : Fin (d + 1)) :
    reducedNormalFlattenCLE (d := d) i j p
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) =
      p.2 k μ := by
  simp only [reducedNormalFlattenCLE, reducedSpectatorFlattenCLE,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply, SCV.finAppendCLE_apply_tail,
    SCV.realBlockFlattenCLE_apply]
  unfold ContinuousLinearEquiv.piCongrLeft LinearEquiv.piCongrLeft
    LinearEquiv.piCongrLeft'
  simp [Equiv.piCongrLeft_apply_apply]

omit [NeZero d] in
/-- In the flattened reduced normal chart, the adjacent sign flip negates the
selected-difference head block. -/
theorem reducedNormalFlattenCLE_signFlip_head
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j) (μ : Fin (d + 1)) :
    reducedNormalFlattenCLE (d := d) i j
        (reducedSignFlip (d := d) i j p)
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) =
      -reducedNormalFlattenCLE (d := d) i j p
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) := by
  simp [reducedSignFlip]

omit [NeZero d] in
/-- In the flattened reduced normal chart, the adjacent sign flip fixes every
frozen spectator coordinate. -/
theorem reducedNormalFlattenCLE_signFlip_tail
    {m : ℕ} (i j : Fin (m + 1))
    (p : ReducedSpace d m i j)
    (k : SpectatorIndex (m + 1) i j) (μ : Fin (d + 1)) :
    reducedNormalFlattenCLE (d := d) i j
        (reducedSignFlip (d := d) i j p)
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) =
      reducedNormalFlattenCLE (d := d) i j p
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) := by
  simp [reducedSignFlip]

omit [NeZero d] in
/-- The reduced sign flip transported to the flattened SCV chart. -/
noncomputable def reducedNormalFlattenedSignFlipCLE
    {m : ℕ} (i j : Fin (m + 1)) :
    (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) ≃L[ℝ]
      (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :=
  ((reducedNormalFlattenCLE (d := d) i j).symm.trans
    (reducedSignFlipCLE (d := d) i j)).trans
      (reducedNormalFlattenCLE (d := d) i j)

omit [NeZero d] in
/-- The flattened transported sign flip negates precisely the
selected-difference head block. -/
theorem reducedNormalFlattenedSignFlipCLE_apply_head
    {m : ℕ} (i j : Fin (m + 1))
    (u : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ)
    (μ : Fin (d + 1)) :
    reducedNormalFlattenedSignFlipCLE (d := d) i j u
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) =
      -u
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) := by
  let e := reducedNormalFlattenCLE (d := d) i j
  let p : ReducedSpace d m i j := e.symm u
  have hp : e p = u := by
    simp [p, e]
  calc
    reducedNormalFlattenedSignFlipCLE (d := d) i j u
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ)
        =
      e (reducedSignFlip (d := d) i j p)
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) := by
        rfl
    _ =
      -e p
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) := by
        exact reducedNormalFlattenCLE_signFlip_head (d := d) i j p μ
    _ =
      -u
        (Fin.castAdd
          (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ) := by
        rw [hp]

omit [NeZero d] in
/-- The flattened transported sign flip fixes the frozen spectator tail block. -/
theorem reducedNormalFlattenedSignFlipCLE_apply_tail
    {m : ℕ} (i j : Fin (m + 1))
    (u : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ)
    (k : SpectatorIndex (m + 1) i j) (μ : Fin (d + 1)) :
    reducedNormalFlattenedSignFlipCLE (d := d) i j u
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) =
      u
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) := by
  let e := reducedNormalFlattenCLE (d := d) i j
  let p : ReducedSpace d m i j := e.symm u
  have hp : e p = u := by
    simp [p, e]
  calc
    reducedNormalFlattenedSignFlipCLE (d := d) i j u
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ)))
        =
      e (reducedSignFlip (d := d) i j p)
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) := by
        rfl
    _ =
      e p
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) := by
        exact reducedNormalFlattenCLE_signFlip_tail (d := d) i j p k μ
    _ =
      u
        (Fin.natAdd (d + 1)
          (finProdFinEquiv
            ((Fintype.equivFin (SpectatorIndex (m + 1) i j) k), μ))) := by
        rw [hp]

omit [NeZero d] in
/-- The flattened selected spacelike collar: only the head block, corresponding
to the selected adjacent difference, is tested for spacelikeness. -/
def reducedNormalFlattenedSelectedSpacelike
    {m : ℕ} (i j : Fin (m + 1)) :
    Set (Fin ((d + 1) +
      Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :=
  {u | MinkowskiSpace.IsSpacelike d
    (fun μ => u (Fin.castAdd
      (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ))}

omit [NeZero d] in
/-- The flattened selected spacelike collar is an open real edge set. -/
theorem isOpen_reducedNormalFlattenedSelectedSpacelike
    {m : ℕ} (i j : Fin (m + 1)) :
    IsOpen (reducedNormalFlattenedSelectedSpacelike (d := d) i j) := by
  have hquad : Continuous
      (fun u : Fin ((d + 1) +
          Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ =>
        MinkowskiSpace.minkowskiNormSq d
          (fun μ => u (Fin.castAdd
            (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ))) := by
    unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
    exact continuous_finset_sum _ fun μ _ =>
      (continuous_const.mul (continuous_apply _)).mul (continuous_apply _)
  simpa [reducedNormalFlattenedSelectedSpacelike,
    MinkowskiSpace.IsSpacelike] using hquad.isOpen_preimage _ isOpen_Ioi

omit [NeZero d] in
/-- Membership in the flattened selected spacelike collar is exactly membership
in the reduced normal selected-spacelike collar after unflattening. -/
theorem reducedNormalFlattenedSelectedSpacelike_iff
    {m : ℕ} (i j : Fin (m + 1))
    (u : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :
    u ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j ↔
      (reducedNormalFlattenCLE (d := d) i j).symm u ∈
        reducedSelectedSpacelike (d := d) i j := by
  change MinkowskiSpace.IsSpacelike d
      (fun μ => u (Fin.castAdd
        (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ)) ↔
    MinkowskiSpace.IsSpacelike d
      ((reducedNormalFlattenCLE (d := d) i j).symm u).1
  constructor <;> intro h
  · simpa [← reducedNormalFlattenCLE_apply_head (d := d) i j
      ((reducedNormalFlattenCLE (d := d) i j).symm u)] using h
  · simpa [← reducedNormalFlattenCLE_apply_head (d := d) i j
      ((reducedNormalFlattenCLE (d := d) i j).symm u),
      (reducedNormalFlattenCLE (d := d) i j).apply_symm_apply u] using h

/-- The flattened selected spacelike collar is invariant under the transported
adjacent sign flip. -/
theorem reducedNormalFlattenedSelectedSpacelike_signFlip_iff
    {m : ℕ} (i j : Fin (m + 1))
    (u : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) :
    reducedNormalFlattenedSignFlipCLE (d := d) i j u ∈
        reducedNormalFlattenedSelectedSpacelike (d := d) i j ↔
      u ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j := by
  change MinkowskiSpace.IsSpacelike d
      (fun μ =>
        reducedNormalFlattenedSignFlipCLE (d := d) i j u
          (Fin.castAdd
            (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ)) ↔
    MinkowskiSpace.IsSpacelike d
      (fun μ =>
        u
          (Fin.castAdd
            (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ))
  simpa [reducedNormalFlattenedSignFlipCLE_apply_head] using
    (minkowski_isSpacelike_neg_iff (d := d)
      (fun μ =>
        u
          (Fin.castAdd
            (Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) μ)))

/-- Every flattened selected spacelike point has an open real-edge collar,
invariant under the transported adjacent sign flip. -/
theorem exists_reducedNormalFlattenedSelectedSpacelike_signFlip_invariant_open_nhds
    {m : ℕ} (i j : Fin (m + 1))
    (u : Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ)
    (hu : u ∈ reducedNormalFlattenedSelectedSpacelike (d := d) i j) :
    ∃ V : Set (Fin ((d + 1) +
        Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ),
      IsOpen V ∧ u ∈ V ∧
        V ⊆ reducedNormalFlattenedSelectedSpacelike (d := d) i j ∧
        (∀ v ∈ V,
          reducedNormalFlattenedSignFlipCLE (d := d) i j v ∈ V) := by
  refine
    ⟨reducedNormalFlattenedSelectedSpacelike (d := d) i j,
      isOpen_reducedNormalFlattenedSelectedSpacelike (d := d) i j,
      hu, subset_rfl, ?_⟩
  intro v hv
  exact
    (reducedNormalFlattenedSelectedSpacelike_signFlip_iff
      (d := d) i j v).2 hv

omit [NeZero d] in
/-- A reduced normal-coordinate Schwartz test supported where the selected
difference is spacelike stays supported in the corresponding flattened SCV
coordinate collar. -/
theorem reducedNormalFlattenedSchwartz_support_subset_selectedSpacelike
    {m : ℕ} (i j : Fin (m + 1))
    (ψ : SchwartzMap (ReducedSpace d m i j) ℂ)
    (hψ_support :
      Function.support (ψ : ReducedSpace d m i j → ℂ) ⊆
        reducedSelectedSpacelike (d := d) i j) :
    Function.support
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (reducedNormalFlattenCLE (d := d) i j).symm) ψ) :
          (Fin ((d + 1) +
            Fintype.card (SpectatorIndex (m + 1) i j) * (d + 1)) → ℝ) → ℂ)
      ⊆ reducedNormalFlattenedSelectedSpacelike (d := d) i j := by
  intro u hu
  have hpre :
      (reducedNormalFlattenCLE (d := d) i j).symm u ∈
        Function.support (ψ : ReducedSpace d m i j → ℂ) := by
    change ψ ((reducedNormalFlattenCLE (d := d) i j).symm u) ≠ 0
    simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hu
  exact
    (reducedNormalFlattenedSelectedSpacelike_iff (d := d) i j u).2
      (hψ_support hpre)

end AdjacentNormal

end OSReconstruction
