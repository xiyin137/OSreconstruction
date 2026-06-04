import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport

/-!
# Adjacent Frozen-Spectator Normal Form

Monograph Vol IV Ch 2, Prop. `os-boundary-package-consequences` (b), and
Jost/Ruelle's local proof freeze the spectator variables and apply the
one-spacelike-difference edge-of-the-wedge argument to the adjacent pair.

This module records the real coordinate normal form behind that step.  In
absolute coordinates, the adjacent transposition fixes the pair center and all
spectator positions measured relative to that center; it only negates the
selected adjacent difference.  This is the coordinate surface the remaining
mixed-tube boundary theorem should use, rather than trying to put the whole
many-point reduced configuration into the PET.
-/

open scoped Classical NNReal

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Spectator labels for an adjacent pair in an absolute `n`-point
configuration. -/
def AdjacentNormal.SpectatorIndex
    (n : ℕ) (i j : Fin n) : Type :=
  {k : Fin n // k ≠ i ∧ k ≠ j}

instance AdjacentNormal.instFintypeSpectatorIndex
    (n : ℕ) (i j : Fin n) :
    Fintype (AdjacentNormal.SpectatorIndex n i j) := by
  classical
  dsimp [AdjacentNormal.SpectatorIndex]
  infer_instance

/-- Center of the selected adjacent pair. -/
def AdjacentNormal.pairCenter
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n) : SpacetimeDim d :=
  fun μ => (x i μ + x j μ) / 2

/-- Difference variable for the selected adjacent pair, in the same orientation
as the reduced adjacent coordinate. -/
def AdjacentNormal.pairDiff
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n) : SpacetimeDim d :=
  fun μ => x j μ - x i μ

/-- A spectator coordinate measured relative to the selected pair center. -/
def AdjacentNormal.spectatorRel
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n)
    (k : AdjacentNormal.SpectatorIndex n i j) : SpacetimeDim d :=
  fun μ => x k.1 μ - AdjacentNormal.pairCenter (d := d) i j x μ

/-- Absolute normal coordinates for a selected adjacent pair: pair center,
selected difference, and all spectators relative to the center. -/
abbrev AdjacentNormal.Space
    (d n : ℕ) (i j : Fin n) : Type :=
  SpacetimeDim d × SpacetimeDim d ×
    (AdjacentNormal.SpectatorIndex n i j → SpacetimeDim d)

/-- The frozen-spectator coordinate map. -/
def AdjacentNormal.coord
    {n : ℕ} (i j : Fin n) (x : NPointDomain d n) :
    AdjacentNormal.Space d n i j :=
  (AdjacentNormal.pairCenter (d := d) i j x,
    AdjacentNormal.pairDiff (d := d) i j x,
    AdjacentNormal.spectatorRel (d := d) i j x)

/- Reconstruct absolute coordinates from frozen-spectator normal coordinates.
The selected pair is placed at center `c ± v/2`, while every spectator is
placed at center plus its frozen relative position. -/
def AdjacentNormal.coordInv
    {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (p : AdjacentNormal.Space d n i j) : NPointDomain d n :=
  fun k μ =>
    if hki : k = i then
      p.1 μ - p.2.1 μ / 2
    else if hkj : k = j then
      p.1 μ + p.2.1 μ / 2
    else
      p.1 μ + p.2.2 ⟨k, hki, hkj⟩ μ

omit [NeZero d] in
/-- The frozen-spectator normal coordinates reconstruct the original absolute
configuration. -/
theorem AdjacentNormal.coordInv_left
    {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : NPointDomain d n) :
    AdjacentNormal.coordInv (d := d) i j hij
        (AdjacentNormal.coord (d := d) i j x) = x := by
  ext k μ
  by_cases hki : k = i
  · subst k
    simp [AdjacentNormal.coordInv, AdjacentNormal.coord,
      AdjacentNormal.pairCenter, AdjacentNormal.pairDiff,
      div_eq_mul_inv]
    ring
  · by_cases hkj : k = j
    · subst k
      simp [AdjacentNormal.coordInv, AdjacentNormal.coord,
        AdjacentNormal.pairCenter, AdjacentNormal.pairDiff,
        hij.symm, div_eq_mul_inv]
      ring
    · simp [AdjacentNormal.coordInv, AdjacentNormal.coord,
        AdjacentNormal.spectatorRel, AdjacentNormal.pairCenter,
        hki, hkj]

omit [NeZero d] in
/-- Absolute reconstruction followed by frozen-spectator coordinates is the
identity.  This is the coordinate isomorphism used in the local Jost/Ruelle
one-difference argument. -/
theorem AdjacentNormal.coordInv_right
    {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (p : AdjacentNormal.Space d n i j) :
    AdjacentNormal.coord (d := d) i j
        (AdjacentNormal.coordInv (d := d) i j hij p) = p := by
  apply Prod.ext
  · ext μ
    simp [AdjacentNormal.coord, AdjacentNormal.coordInv,
      AdjacentNormal.pairCenter, hij.symm, div_eq_mul_inv]
    ring
  · apply Prod.ext
    · ext μ
      simp [AdjacentNormal.coord, AdjacentNormal.coordInv,
        AdjacentNormal.pairDiff, hij.symm, div_eq_mul_inv]
      ring
    · funext k
      ext μ
      simp [AdjacentNormal.coord, AdjacentNormal.coordInv,
        AdjacentNormal.spectatorRel, AdjacentNormal.pairCenter,
        k.2.1, k.2.2, hij.symm, div_eq_mul_inv]
      ring

omit [NeZero d] in
/-- The inverse frozen-spectator coordinate map is continuous. -/
theorem AdjacentNormal.continuous_coordInv
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Continuous (fun p : AdjacentNormal.Space d n i j =>
      AdjacentNormal.coordInv (d := d) i j hij p) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  have hc : Continuous (fun p : AdjacentNormal.Space d n i j => p.1 μ) :=
    (continuous_apply μ).comp continuous_fst
  have hv : Continuous (fun p : AdjacentNormal.Space d n i j => p.2.1 μ) :=
    (continuous_apply μ).comp (continuous_fst.comp continuous_snd)
  by_cases hki : k = i
  · simpa [AdjacentNormal.coordInv, hki, div_eq_mul_inv] using
      hc.sub (hv.mul_const ((2 : ℝ)⁻¹))
  · by_cases hkj : k = j
    · simpa [AdjacentNormal.coordInv, hki, hkj, hij.symm, div_eq_mul_inv] using
        hc.add (hv.mul_const ((2 : ℝ)⁻¹))
    · have hr :
          Continuous (fun p : AdjacentNormal.Space d n i j =>
            p.2.2 ⟨k, hki, hkj⟩ μ) :=
        (continuous_apply μ).comp
          ((continuous_apply
              (⟨k, hki, hkj⟩ : AdjacentNormal.SpectatorIndex n i j)).comp
            (continuous_snd.comp continuous_snd))
      simpa [AdjacentNormal.coordInv, hki, hkj] using
        hc.add hr

omit [NeZero d] in
/-- The frozen-spectator normal-coordinate map is a real linear equivalence.
This is the finite-dimensional change of variables needed to move Schwartz
tests into the product coordinates used by the local one-difference EOW
argument. -/
noncomputable def AdjacentNormal.coordLinearEquiv
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    NPointDomain d n ≃ₗ[ℝ] AdjacentNormal.Space d n i j where
  toFun := AdjacentNormal.coord (d := d) i j
  invFun := AdjacentNormal.coordInv (d := d) i j hij
  left_inv := AdjacentNormal.coordInv_left (d := d) i j hij
  right_inv := AdjacentNormal.coordInv_right (d := d) i j hij
  map_add' := by
    intro x y
    apply Prod.ext
    · ext μ
      simp [AdjacentNormal.coord, AdjacentNormal.pairCenter,
        Pi.add_apply, div_eq_mul_inv]
      ring
    · apply Prod.ext
      · ext μ
        simp [AdjacentNormal.coord, AdjacentNormal.pairDiff,
          Pi.add_apply]
        ring
      · funext k
        ext μ
        simp [AdjacentNormal.coord, AdjacentNormal.spectatorRel,
          AdjacentNormal.pairCenter, Pi.add_apply, div_eq_mul_inv]
        ring
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext μ
      simp [AdjacentNormal.coord, AdjacentNormal.pairCenter,
        Pi.smul_apply, div_eq_mul_inv]
      ring
    · apply Prod.ext
      · ext μ
        simp [AdjacentNormal.coord, AdjacentNormal.pairDiff,
          Pi.smul_apply]
        ring
      · funext k
        ext μ
        simp [AdjacentNormal.coord, AdjacentNormal.spectatorRel,
          AdjacentNormal.pairCenter, Pi.smul_apply, div_eq_mul_inv]
        ring

omit [NeZero d] in
/-- Continuous-linear version of the frozen-spectator normal coordinates, ready
for Schwartz pullback. -/
noncomputable def AdjacentNormal.coordCLE
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    NPointDomain d n ≃L[ℝ] AdjacentNormal.Space d n i j :=
  (AdjacentNormal.coordLinearEquiv (d := d) i j hij).toContinuousLinearEquiv

omit [NeZero d] in
/-- The normal-form action of the adjacent transposition: keep the center and
spectators fixed and reflect the selected difference. -/
def AdjacentNormal.signFlip
    {n : ℕ} (i j : Fin n)
    (p : AdjacentNormal.Space d n i j) :
    AdjacentNormal.Space d n i j :=
  (p.1, -p.2.1, p.2.2)

omit [NeZero d] in
/-- The selected spacelike collar in frozen-spectator normal coordinates. -/
def AdjacentNormal.selectedSpacelike
    {n : ℕ} (i j : Fin n) :
    Set (AdjacentNormal.Space d n i j) :=
  {p | MinkowskiSpace.IsSpacelike d p.2.1}

omit [NeZero d] in
/-- The normal-form adjacent sign flip is a real linear involution. -/
noncomputable def AdjacentNormal.signFlipLinearEquiv
    {n : ℕ} (i j : Fin n) :
    AdjacentNormal.Space d n i j ≃ₗ[ℝ]
      AdjacentNormal.Space d n i j where
  toFun := AdjacentNormal.signFlip (d := d) i j
  invFun := AdjacentNormal.signFlip (d := d) i j
  left_inv := by
    intro p
    ext <;> simp [AdjacentNormal.signFlip]
  right_inv := by
    intro p
    ext <;> simp [AdjacentNormal.signFlip]
  map_add' := by
    intro p q
    apply Prod.ext
    · ext μ
      simp [AdjacentNormal.signFlip]
    · apply Prod.ext
      · ext μ
        simp [AdjacentNormal.signFlip]
        ring
      · funext k
        ext μ
        simp [AdjacentNormal.signFlip]
  map_smul' := by
    intro a p
    ext <;> simp [AdjacentNormal.signFlip]

omit [NeZero d] in
/-- Continuous-linear version of the normal-form adjacent sign flip. -/
noncomputable def AdjacentNormal.signFlipCLE
    {n : ℕ} (i j : Fin n) :
    AdjacentNormal.Space d n i j ≃L[ℝ]
      AdjacentNormal.Space d n i j :=
  { toLinearEquiv := AdjacentNormal.signFlipLinearEquiv (d := d) i j
    continuous_toFun := by
      change Continuous
        (fun p : AdjacentNormal.Space d n i j =>
          AdjacentNormal.signFlip (d := d) i j p)
      have hc : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.1) :=
        continuous_fst
      have hv : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.2.1) :=
        continuous_fst.comp continuous_snd
      have hs : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.2.2) :=
        continuous_snd.comp continuous_snd
      simpa [AdjacentNormal.signFlip] using
        hc.prodMk (hv.neg.prodMk hs)
    continuous_invFun := by
      change Continuous
        (fun p : AdjacentNormal.Space d n i j =>
          AdjacentNormal.signFlip (d := d) i j p)
      have hc : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.1) :=
        continuous_fst
      have hv : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.2.1) :=
        continuous_fst.comp continuous_snd
      have hs : Continuous
          (fun p : AdjacentNormal.Space d n i j => p.2.2) :=
        continuous_snd.comp continuous_snd
      simpa [AdjacentNormal.signFlip] using
        hc.prodMk (hv.neg.prodMk hs) }

omit [NeZero d] in
/-- Adjacent swapping fixes the selected pair center. -/
theorem AdjacentNormal.pairCenter_swap_eq
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) :
    AdjacentNormal.pairCenter (d := d) i ⟨i.val + 1, hi⟩
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      AdjacentNormal.pairCenter (d := d) i ⟨i.val + 1, hi⟩ x := by
  ext μ
  simp [AdjacentNormal.pairCenter, add_comm]

omit [NeZero d] in
/-- Adjacent swapping negates the selected pair difference. -/
theorem AdjacentNormal.pairDiff_swap_eq_neg
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) :
    AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      -AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x := by
  ext μ
  simp [AdjacentNormal.pairDiff]

omit [NeZero d] in
/-- Adjacent swapping fixes every spectator coordinate relative to the selected
pair center. -/
theorem AdjacentNormal.spectatorRel_swap_eq
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (k : AdjacentNormal.SpectatorIndex n i ⟨i.val + 1, hi⟩) :
    AdjacentNormal.spectatorRel (d := d) i ⟨i.val + 1, hi⟩
        (fun a => x (Equiv.swap i ⟨i.val + 1, hi⟩ a)) k =
      AdjacentNormal.spectatorRel (d := d) i ⟨i.val + 1, hi⟩ x k := by
  ext μ
  have hk :
      Equiv.swap i ⟨i.val + 1, hi⟩ k.1 = k.1 := by
    exact Equiv.swap_apply_of_ne_of_ne k.2.1 k.2.2
  simp [AdjacentNormal.spectatorRel,
    AdjacentNormal.pairCenter_swap_eq (d := d) i hi x, hk]

omit [NeZero d] in
/-- In frozen-spectator coordinates, an adjacent transposition fixes the
center and spectators and only negates the selected spacelike coordinate. -/
theorem AdjacentNormal.coord_swap_eq
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) :
    AdjacentNormal.coord (d := d) i ⟨i.val + 1, hi⟩
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      (AdjacentNormal.pairCenter (d := d) i ⟨i.val + 1, hi⟩ x,
        -AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x,
        AdjacentNormal.spectatorRel (d := d) i ⟨i.val + 1, hi⟩ x) := by
  ext <;> simp [AdjacentNormal.coord,
    AdjacentNormal.pairCenter_swap_eq (d := d) i hi x,
    AdjacentNormal.pairDiff_swap_eq_neg (d := d) i hi x,
    AdjacentNormal.spectatorRel_swap_eq (d := d) i hi x]

omit [NeZero d] in
/-- In normal coordinates, the adjacent transposition is exactly the sign flip
on the selected difference coordinate. -/
theorem AdjacentNormal.coord_swap_eq_signFlip
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) :
    AdjacentNormal.coord (d := d) i ⟨i.val + 1, hi⟩
        (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) =
      AdjacentNormal.signFlip (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.coord (d := d) i ⟨i.val + 1, hi⟩ x) := by
  rw [AdjacentNormal.coord_swap_eq (d := d) i hi x]
  rfl

private theorem AdjacentNormal.adjacent_succ_ne
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    i ≠ ⟨i.val + 1, hi⟩ := by
  intro h
  have hv : i.val = i.val + 1 := by
    simpa using congrArg Fin.val h
  omega

omit [NeZero d] in
/-- The inverse normal chart intertwines the normal sign flip with the absolute
adjacent transposition. -/
theorem AdjacentNormal.coordInv_signFlip_eq_swap
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (p : AdjacentNormal.Space d n i ⟨i.val + 1, hi⟩) :
    AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.adjacent_succ_ne i hi)
        (AdjacentNormal.signFlip (d := d) i ⟨i.val + 1, hi⟩ p)
      =
    (fun k =>
      (AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.adjacent_succ_ne i hi)
        p) (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
  let j : Fin n := ⟨i.val + 1, hi⟩
  have hij : i ≠ j := AdjacentNormal.adjacent_succ_ne i hi
  let x : NPointDomain d n :=
    AdjacentNormal.coordInv (d := d) i j hij p
  have hchart :
      AdjacentNormal.coord (d := d) i j
          (fun k => x (Equiv.swap i j k)) =
        AdjacentNormal.signFlip (d := d) i j p := by
    have hswap :=
      AdjacentNormal.coord_swap_eq_signFlip (d := d) i hi x
    simpa [x, j, hij,
      AdjacentNormal.coordInv_right (d := d) i j hij p] using hswap
  have hinv := congrArg
    (AdjacentNormal.coordInv (d := d) i j hij) hchart
  have hleft :
      AdjacentNormal.coordInv (d := d) i j hij
          (AdjacentNormal.coord (d := d) i j
            (fun k => x (Equiv.swap i j k))) =
        (fun k => x (Equiv.swap i j k)) :=
    AdjacentNormal.coordInv_left (d := d) i j hij
      (fun k => x (Equiv.swap i j k))
  have hres :
      (fun k => x (Equiv.swap i j k)) =
        AdjacentNormal.coordInv (d := d) i j hij
          (AdjacentNormal.signFlip (d := d) i j p) := by
    exact hleft.symm.trans hinv
  simpa [x, j, hij] using hres.symm

/-- The selected spacelike normal collar is invariant under the normal-form
adjacent sign flip. -/
theorem AdjacentNormal.selectedSpacelike_signFlip_iff
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (p : AdjacentNormal.Space d n i ⟨i.val + 1, hi⟩) :
    AdjacentNormal.signFlip (d := d) i ⟨i.val + 1, hi⟩ p ∈
        AdjacentNormal.selectedSpacelike (d := d) i ⟨i.val + 1, hi⟩ ↔
      p ∈ AdjacentNormal.selectedSpacelike (d := d) i ⟨i.val + 1, hi⟩ := by
  change MinkowskiSpace.IsSpacelike d (-p.2.1) ↔
    MinkowskiSpace.IsSpacelike d p.2.1
  exact minkowski_isSpacelike_neg_iff (d := d) p.2.1

omit [NeZero d] in
/-- Pulling a Schwartz test into frozen-spectator coordinates converts the
absolute adjacent swap into the normal sign flip. -/
theorem AdjacentNormal.schwartz_signFlip_pullback_apply
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (f : SchwartzNPoint d n)
    (p : AdjacentNormal.Space d n i ⟨i.val + 1, hi⟩) :
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (AdjacentNormal.signFlipCLE (d := d) i ⟨i.val + 1, hi⟩))
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (AdjacentNormal.coordCLE (d := d) i ⟨i.val + 1, hi⟩
          (AdjacentNormal.adjacent_succ_ne i hi)).symm) f)) p =
      f (fun k =>
        (AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
          (AdjacentNormal.adjacent_succ_ne i hi) p)
          (Equiv.swap i ⟨i.val + 1, hi⟩ k)) := by
  change
    f (AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
        (AdjacentNormal.adjacent_succ_ne i hi)
        (AdjacentNormal.signFlip (d := d) i ⟨i.val + 1, hi⟩ p)) =
      f (fun k =>
        (AdjacentNormal.coordInv (d := d) i ⟨i.val + 1, hi⟩
          (AdjacentNormal.adjacent_succ_ne i hi) p)
          (Equiv.swap i ⟨i.val + 1, hi⟩ k))
  rw [AdjacentNormal.coordInv_signFlip_eq_swap (d := d) i hi p]

/-- A test supported on an adjacent spacelike absolute pair pulls back to a
normal-coordinate test supported where the selected normal difference is
spacelike. -/
theorem AdjacentNormal.schwartz_support_subset_selectedSpacelike
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (f : SchwartzNPoint d n)
    (hf_spacelike : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩)) :
    Function.support
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (AdjacentNormal.coordCLE (d := d) i ⟨i.val + 1, hi⟩
            (AdjacentNormal.adjacent_succ_ne i hi)).symm) f) :
          AdjacentNormal.Space d n i ⟨i.val + 1, hi⟩ → ℂ)
      ⊆ AdjacentNormal.selectedSpacelike
          (d := d) i ⟨i.val + 1, hi⟩ := by
  intro p hp
  let j : Fin n := ⟨i.val + 1, hi⟩
  let hij : i ≠ j := AdjacentNormal.adjacent_succ_ne i hi
  let x : NPointDomain d n :=
    AdjacentNormal.coordInv (d := d) i j hij p
  have hfx : f.toFun x ≠ 0 := by
    change
      (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (AdjacentNormal.coordCLE (d := d) i j hij).symm) f) p) ≠ 0
    simpa [x, j, hij, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hp
  have hsp_diff :
      MinkowskiSpace.IsSpacelike d
        (AdjacentNormal.pairDiff (d := d) i j x) := by
    have hbase :
        MinkowskiSpace.IsSpacelike d (fun μ => x i μ - x j μ) := by
      simpa [MinkowskiSpace.AreSpacelikeSeparated, Pi.sub_apply, j] using
        hf_spacelike x (by simpa [x] using hfx)
    have hneg :=
      (minkowski_isSpacelike_neg_iff (d := d)
        (fun μ => x i μ - x j μ)).2 hbase
    have hdiff :
        AdjacentNormal.pairDiff (d := d) i j x =
          -(fun μ => x i μ - x j μ) := by
      ext μ
      simp [AdjacentNormal.pairDiff]
    rw [hdiff]
    exact hneg
  have hcoord :
      AdjacentNormal.pairDiff (d := d) i j x = p.2.1 := by
    have hright :=
      AdjacentNormal.coordInv_right (d := d) i j hij p
    exact congrArg (fun q : AdjacentNormal.Space d n i j => q.2.1)
      hright
  change MinkowskiSpace.IsSpacelike d p.2.1
  simpa [hcoord] using hsp_diff

omit [NeZero d] in
theorem AdjacentNormal.continuous_pairCenter
    {n : ℕ} (i j : Fin n) :
    Continuous (fun x : NPointDomain d n =>
      AdjacentNormal.pairCenter (d := d) i j x) := by
  apply continuous_pi
  intro μ
  have hi_cont : Continuous (fun x : NPointDomain d n => x i μ) :=
    (continuous_apply μ).comp (continuous_apply i)
  have hj_cont : Continuous (fun x : NPointDomain d n => x j μ) :=
    (continuous_apply μ).comp (continuous_apply j)
  have hsum : Continuous (fun x : NPointDomain d n => x i μ + x j μ) :=
    hi_cont.add hj_cont
  simpa [AdjacentNormal.pairCenter, div_eq_mul_inv] using
    hsum.mul_const ((2 : ℝ)⁻¹)

omit [NeZero d] in
theorem AdjacentNormal.continuous_pairDiff
    {n : ℕ} (i j : Fin n) :
    Continuous (fun x : NPointDomain d n =>
      AdjacentNormal.pairDiff (d := d) i j x) := by
  apply continuous_pi
  intro μ
  have hj_cont : Continuous (fun x : NPointDomain d n => x j μ) :=
    (continuous_apply μ).comp (continuous_apply j)
  have hi_cont : Continuous (fun x : NPointDomain d n => x i μ) :=
    (continuous_apply μ).comp (continuous_apply i)
  simpa [AdjacentNormal.pairDiff] using
    hj_cont.sub hi_cont

omit [NeZero d] in
theorem AdjacentNormal.continuous_spectatorRel
    {n : ℕ} (i j : Fin n)
    (k : AdjacentNormal.SpectatorIndex n i j) :
    Continuous (fun x : NPointDomain d n =>
      AdjacentNormal.spectatorRel (d := d) i j x k) := by
  apply continuous_pi
  intro μ
  have hk_cont : Continuous (fun x : NPointDomain d n => x k.1 μ) :=
    (continuous_apply μ).comp (continuous_apply k.1)
  have hcenter_cont :
      Continuous (fun x : NPointDomain d n =>
        AdjacentNormal.pairCenter (d := d) i j x μ) :=
    (continuous_apply μ).comp
      (AdjacentNormal.continuous_pairCenter (d := d) i j)
  simpa [AdjacentNormal.spectatorRel] using
    hk_cont.sub hcenter_cont

omit [NeZero d] in
/-- The frozen-spectator coordinate map is continuous.  This is the topological
input needed before pulling compact Schwartz tests into these coordinates. -/
theorem AdjacentNormal.continuous_coord
    {n : ℕ} (i j : Fin n) :
    Continuous (fun x : NPointDomain d n =>
      AdjacentNormal.coord (d := d) i j x) := by
  refine
    (AdjacentNormal.continuous_pairCenter (d := d) i j).prodMk
      ((AdjacentNormal.continuous_pairDiff (d := d) i j).prodMk ?_)
  apply continuous_pi
  intro k
  exact AdjacentNormal.continuous_spectatorRel (d := d) i j k

omit [NeZero d] in
/-- The active normal coordinate has an open spacelike collar. -/
theorem AdjacentNormal.isOpen_pairDiff_spacelike
    {n : ℕ} (i j : Fin n) :
    IsOpen
      {x : NPointDomain d n |
        MinkowskiSpace.IsSpacelike d
          (AdjacentNormal.pairDiff (d := d) i j x)} := by
  have hquad : Continuous (fun x : NPointDomain d n =>
      MinkowskiSpace.minkowskiNormSq d
        (AdjacentNormal.pairDiff (d := d) i j x)) :=
    by
      have hdiff := AdjacentNormal.continuous_pairDiff (d := d) i j
      unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
      exact continuous_finset_sum _ fun μ _ =>
        (continuous_const.mul ((continuous_apply μ).comp hdiff)).mul
          ((continuous_apply μ).comp hdiff)
  simpa [MinkowskiSpace.IsSpacelike] using
    isOpen_lt continuous_const hquad

/-- The adjacent swap preserves the active spacelike collar in normal
coordinates because it only negates the selected difference. -/
theorem AdjacentNormal.pairDiff_spacelike_swap_iff
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n) :
    MinkowskiSpace.IsSpacelike d
        (AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩
          (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) ↔
      MinkowskiSpace.IsSpacelike d
        (AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x) := by
  rw [AdjacentNormal.pairDiff_swap_eq_neg (d := d) i hi x]
  exact minkowski_isSpacelike_neg_iff
    (d := d) (AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x)

/-- Spacelike separation of the adjacent pair is exactly spacelikeness of the
normal-form selected difference, up to the harmless orientation sign. -/
theorem AdjacentNormal.pairDiff_spacelike_of_areSpacelikeSeparated
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (x : NPointDomain d n)
    (hsp :
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩)) :
    MinkowskiSpace.IsSpacelike d
      (AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x) := by
  have hbase :
      MinkowskiSpace.IsSpacelike d
        (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) := by
    simpa [MinkowskiSpace.AreSpacelikeSeparated, Pi.sub_apply] using hsp
  have hneg :=
    (minkowski_isSpacelike_neg_iff (d := d)
      (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ)).2 hbase
  have hdiff :
      AdjacentNormal.pairDiff (d := d) i ⟨i.val + 1, hi⟩ x =
        -(fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) := by
    ext μ
    simp [AdjacentNormal.pairDiff]
  rw [hdiff]
  exact hneg

end OSReconstruction
