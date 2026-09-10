/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison










open scoped Classical NNReal
open BigOperators
open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The canonical reduced imaginary direction: every reduced difference slot
uses the fixed future-timelike safe basepoint vector. -/
def canonicalReducedDirection (m : ℕ) : Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

/-- The canonical reduced direction lies in the product forward cone. -/
theorem canonicalReducedDirection_mem_productForwardConeReal
    (m : ℕ) :
    canonicalReducedDirection (d := d) m ∈ BHW.ProductForwardConeReal d m := by
  intro _k
  exact BHW.safeBasepointVec_mem_forwardCone (d := d)

omit [NeZero d] in
/-- The induced reduced permutation sends real reduced configurations to real
reduced configurations. -/
theorem permOnReducedDiff_ofReal_im_zero
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) (ξ : NPointDomain d m) :
    ∀ k μ,
      (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (fun k μ => (ξ k μ : ℂ)) k μ).im = 0 := by
  intro k μ
  let x : NPointDomain d (m + 1) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m 0 ξ)
  let z : Fin (m + 1) → Fin (d + 1) → ℂ := fun k μ => (x k μ : ℂ)
  have hz_red :
      BHW.reducedDiffMap (m + 1) d z =
        fun k μ => (ξ k μ : ℂ) := by
    ext j μ
    rw [BHW.reducedDiffMap_eq_successive_differences]
    change (x ⟨j.val + 1, by omega⟩ μ : ℂ) -
        (x ⟨j.val, by omega⟩ μ : ℂ) = (ξ j μ : ℂ)
    have hreal :
        x ⟨j.val + 1, by omega⟩ μ - x ⟨j.val, by omega⟩ μ =
          ξ j μ := by
      simpa [x, BHW.reducedDiffMapReal_apply] using
        congrFun
          (congrFun
            (BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
              (d := d) (m := m) (0 : SpacetimeDim d) ξ) j) μ
    exact_mod_cast hreal
  have hperm :
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (fun k μ => (ξ k μ : ℂ)) =
        BHW.reducedDiffMap (m + 1) d (fun k => z (σ k)) := by
    calc
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (fun k μ => (ξ k μ : ℂ))
          =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d z) := by
            exact congrArg
              (fun y => BHW.permOnReducedDiff (d := d) (n := m + 1) σ y)
              hz_red.symm
      _ = BHW.reducedDiffMap (m + 1) d (fun k => z (σ k)) := by
            exact BHW.permOnReducedDiff_reducedDiffMap
              (d := d) (n := m + 1) σ z
  rw [hperm]
  rw [BHW.reducedDiffMap_eq_successive_differences]
  simp [z]

/-- Pair difference read from reduced real coordinates by reconstructing an
absolute representative with basepoint `0`. -/
def reducedPairDiff
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) : Fin (d + 1) → ℝ :=
  fun μ =>
    ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) j μ) -
      ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ) i μ)

omit [NeZero d] in
private noncomputable def prependBasepointRealZeroCLM
    (m : ℕ) :
    NPointDomain d m →L[ℝ] NPointDomain d (m + 1) :=
  ContinuousLinearMap.pi fun k =>
    if hk : k.val = 0 then 0
    else
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => Fin (d + 1) → ℝ) ⟨k.val - 1, by omega⟩

omit [NeZero d] in
private theorem prependBasepointRealZeroCLM_apply
    (m : ℕ) (ξ : NPointDomain d m) :
    prependBasepointRealZeroCLM (d := d) m ξ =
      BHW.prependBasepointReal d m 0 ξ := by
  ext k μ
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := Fin.ext hk
    simp [prependBasepointRealZeroCLM, BHW.prependBasepointReal, hk0]
  · have hk0 : k ≠ 0 := by
      intro h
      exact hk (congrArg Fin.val h)
    simp [prependBasepointRealZeroCLM, BHW.prependBasepointReal, hk, hk0]

omit [NeZero d] in
/-- The selected pair difference as a continuous real-linear map on reduced
difference coordinates.  This is the smearing map used by the Ruelle/Jost
distributional locality step. -/
noncomputable def reducedPairDiffCLM
    (m : ℕ) (i j : Fin (m + 1)) :
    NPointDomain d m →L[ℝ] (Fin (d + 1) → ℝ) :=
  let reconstruct : NPointDomain d m →L[ℝ] NPointDomain d (m + 1) :=
    ((BHW.realDiffCoordCLE (m + 1) d).symm.toContinuousLinearMap).comp
      (prependBasepointRealZeroCLM (d := d) m)
  ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1))
      (φ := fun _ => Fin (d + 1) → ℝ) j) -
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1))
      (φ := fun _ => Fin (d + 1) → ℝ) i)).comp reconstruct

omit [NeZero d] in
@[simp] theorem reducedPairDiffCLM_apply
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) :
    reducedPairDiffCLM (d := d) m i j ξ =
      reducedPairDiff (d := d) m i j ξ := by
  ext μ
  simp [reducedPairDiffCLM, prependBasepointRealZeroCLM_apply,
    reducedPairDiff]

private theorem realDiffCoordCLE_symm_prepend_reducedDiffMapReal_eq_sub_basepoint
    (m : ℕ) (x : NPointDomain d (m + 1)) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0
          (BHW.reducedDiffMapReal (m + 1) d x)) =
      fun k μ => x k μ - x 0 μ := by
  have _ : NeZero d := inferInstance
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
  rw [← hy]
  exact (BHW.realDiffCoordCLE (m + 1) d).symm_apply_apply y

/-- Reconstructing from the reduced real differences preserves every pair
difference. -/
theorem reducedPairDiff_reducedDiffMapReal
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1)) :
    reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x) =
      fun μ => x j μ - x i μ := by
  have hrec :=
    realDiffCoordCLE_symm_prepend_reducedDiffMapReal_eq_sub_basepoint
      (d := d) m x
  ext μ
  change
    ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0
          (BHW.reducedDiffMapReal (m + 1) d x)) j μ) -
      ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0
          (BHW.reducedDiffMapReal (m + 1) d x)) i μ) =
      x j μ - x i μ
  rw [hrec]
  ring

/-- The real reduced edge on which the selected absolute pair is spacelike. -/
def reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) : Set (NPointDomain d m) :=
  {ξ | MinkowskiSpace.IsSpacelike d (reducedPairDiff (d := d) m i j ξ)}

private theorem continuous_minkowskiNormSq :
    Continuous (fun ζ : Fin (d + 1) → ℝ =>
      MinkowskiSpace.minkowskiNormSq d ζ) := by
  have _ : NeZero d := inferInstance
  unfold MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  exact continuous_finset_sum _ (fun μ _ =>
    (continuous_const.mul (continuous_apply μ)).mul (continuous_apply μ))

omit [NeZero d] in
private theorem continuous_reducedPairDiff
    (m : ℕ) (i j : Fin (m + 1)) :
    Continuous (reducedPairDiff (d := d) m i j) := by
  have hfun :
      (fun ξ : NPointDomain d m => reducedPairDiffCLM (d := d) m i j ξ) =
        reducedPairDiff (d := d) m i j := by
    funext ξ
    exact reducedPairDiffCLM_apply (d := d) m i j ξ
  rw [← hfun]
  exact (reducedPairDiffCLM (d := d) m i j).continuous

omit [NeZero d] in
/-- The selected reduced spacelike edge is exactly the preimage of the
spacelike cone under the selected pair-difference continuous-linear map. -/
theorem reducedSpacelikeSwapEdge_eq_preimage_pairDiffCLM
    (m : ℕ) (i j : Fin (m + 1)) :
    reducedSpacelikeSwapEdge (d := d) m i j =
      (reducedPairDiffCLM (d := d) m i j) ⁻¹'
        {v : Fin (d + 1) → ℝ | MinkowskiSpace.IsSpacelike d v} := by
  ext ξ
  simp [reducedSpacelikeSwapEdge]

omit [NeZero d] in
/-- In reduced coordinates, the adjacent pair-difference map is the selected
successive-difference coordinate.  This is the coordinate used for the
book-faithful Ruelle/Jost smearing step. -/
theorem reducedPairDiffCLM_adjacent_eq_proj
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    reducedPairDiffCLM (d := d) m i ⟨i.val + 1, hi⟩ =
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => Fin (d + 1) → ℝ) ⟨i.val, by omega⟩ := by
  ext ξ μ
  change reducedPairDiffCLM (d := d) m i ⟨i.val + 1, hi⟩ ξ μ =
    ξ ⟨i.val, by omega⟩ μ
  rw [reducedPairDiffCLM_apply]
  unfold reducedPairDiff
  have hred :=
    congrFun
      (congrFun
        (BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
          d m (0 : SpacetimeDim d) ξ) ⟨i.val, by omega⟩) μ
  simpa [BHW.reducedDiffMapReal_apply] using hred

omit [NeZero d] in
/-- For adjacent pairs, the selected spacelike reduced edge is the preimage of
the spacelike cone under the selected reduced coordinate projection. -/
theorem reducedSpacelikeSwapEdge_adjacent_eq_preimage_proj
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ =
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => Fin (d + 1) → ℝ) ⟨i.val, by omega⟩) ⁻¹'
        {v : Fin (d + 1) → ℝ | MinkowskiSpace.IsSpacelike d v} := by
  rw [reducedSpacelikeSwapEdge_eq_preimage_pairDiffCLM]
  rw [reducedPairDiffCLM_adjacent_eq_proj]

omit [NeZero d] in
/-- Adjacent reduced edge membership is exactly spacelikeness of the selected
successive-difference coordinate. -/
theorem mem_reducedSpacelikeSwapEdge_adjacent_iff
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    ξ ∈ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ ↔
      MinkowskiSpace.IsSpacelike d (ξ ⟨i.val, by omega⟩) := by
  rw [reducedSpacelikeSwapEdge_adjacent_eq_preimage_proj]
  rfl

omit [NeZero d] in
/-- Replace one reduced successive-difference coordinate.  This is the
coordinate-level map used in the Ruelle/Jost smearing step after the adjacent
spacelike pair has been identified with a single reduced coordinate. -/
def replaceReducedCoord
    (m : ℕ) (q : Fin m) (ξ : NPointDomain d m)
    (v : Fin (d + 1) → ℝ) : NPointDomain d m :=
  Function.update ξ q v

omit [NeZero d] in
/-- The coordinate-replacement map is continuous in both the base reduced
configuration and the selected spacelike coordinate. -/
theorem continuous_replaceReducedCoord
    (m : ℕ) (q : Fin m) :
    Continuous (fun p : NPointDomain d m × (Fin (d + 1) → ℝ) =>
      replaceReducedCoord (d := d) m q p.1 p.2) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro μ
  by_cases hrq : r = q
  · subst hrq
    simpa [replaceReducedCoord] using
      ((continuous_apply μ).comp continuous_snd)
  · simpa [replaceReducedCoord, hrq] using
      ((continuous_apply μ).comp ((continuous_apply r).comp continuous_fst))

/-- The selected reduced spacelike edge is open. -/
theorem isOpen_reducedSpacelikeSwapEdge
    (m : ℕ) (i j : Fin (m + 1)) :
    IsOpen (reducedSpacelikeSwapEdge (d := d) m i j) := by
  have hquad : Continuous (fun ξ : NPointDomain d m =>
      MinkowskiSpace.minkowskiNormSq d (reducedPairDiff (d := d) m i j ξ)) :=
    continuous_minkowskiNormSq (d := d).comp
      (continuous_reducedPairDiff (d := d) m i j)
  simpa [reducedSpacelikeSwapEdge, MinkowskiSpace.IsSpacelike] using
    isOpen_lt continuous_const hquad

omit [NeZero d] in
/-- In successive-difference coordinates, swapping adjacent absolute points
negates the selected adjacent difference.  This is the reduced-coordinate
algebra used in the classical adjacent-transposition locality proof. -/
theorem permOnReducedDiff_adjacentSwap_selected
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ζ : BHW.ReducedNPointConfig d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩) ζ
        ⟨i.val, by omega⟩ =
      -ζ ⟨i.val, by omega⟩ := by
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.reducedDiffSection (m + 1) d ζ
  have hzred : BHW.reducedDiffMap (m + 1) d z = ζ := by
    simpa [z] using BHW.reducedDiffMap_section (m + 1) d ζ
  have hperm :=
    BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z
  ext μ
  have hstep :
      BHW.reducedDiffMap (m + 1) d (fun k => z (σ k))
          ⟨i.val, by omega⟩ μ =
        z i μ - z ⟨i.val + 1, hi⟩ μ := by
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnext :
        (⟨(⟨i.val, by omega⟩ : Fin m).val + 1, by omega⟩ :
          Fin (m + 1)) = ⟨i.val + 1, hi⟩ := by
      ext
      simp
    have hcur :
        (⟨(⟨i.val, by omega⟩ : Fin m).val, by omega⟩ :
          Fin (m + 1)) = i := by
      ext
      simp
    rw [hnext, hcur]
    simp [σ]
  have hζ :
      ζ ⟨i.val, by omega⟩ μ =
        z ⟨i.val + 1, hi⟩ μ - z i μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ
        ⟨i.val, by omega⟩ μ
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d z) ⟨i.val, by omega⟩ μ := by
          rw [hzred]
    _ =
      BHW.reducedDiffMap (m + 1) d (fun k => z (σ k))
        ⟨i.val, by omega⟩ μ := by
          rw [hperm]
    _ = z i μ - z ⟨i.val + 1, hi⟩ μ := hstep
    _ = -ζ ⟨i.val, by omega⟩ μ := by
          rw [hζ]
          ring

private theorem minkowski_isSpacelike_neg_iff
    (v : MinkowskiSpace d) :
    MinkowskiSpace.IsSpacelike d (-v) ↔
      MinkowskiSpace.IsSpacelike d v := by
  unfold MinkowskiSpace.IsSpacelike MinkowskiSpace.minkowskiNormSq
  rw [MinkowskiSpace.minkowskiInner_neg_left,
    MinkowskiSpace.minkowskiInner_neg_right]
  ring_nf

/-- Absolute adjacent spacelike separation descends to the reduced real
spacelike edge.  The sign difference comes from the `j - i` convention in
`reducedPairDiff`; the Minkowski spacelike condition is invariant under
negation. -/
theorem reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
    (m : ℕ) (i j : Fin (m + 1)) (x : NPointDomain d (m + 1))
    (hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) :
    BHW.reducedDiffMapReal (m + 1) d x ∈
      reducedSpacelikeSwapEdge (d := d) m i j := by
  have hbase :
      MinkowskiSpace.IsSpacelike d (fun μ => x i μ - x j μ) := by
    simpa [MinkowskiSpace.AreSpacelikeSeparated, Pi.sub_apply] using hsp
  have hneg :
      MinkowskiSpace.IsSpacelike d (fun μ => x j μ - x i μ) := by
    have h := (minkowski_isSpacelike_neg_iff (d := d)
      (fun μ => x i μ - x j μ)).2 hbase
    have hfun :
        (fun μ => x j μ - x i μ) =
          -(fun μ => x i μ - x j μ) := by
      funext μ
      simp
    rw [hfun]
    exact h
  have hred := reducedPairDiff_reducedDiffMapReal (d := d) m i j x
  change
    MinkowskiSpace.IsSpacelike d
      (reducedPairDiff (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x))
  rw [hred]
  exact hneg

