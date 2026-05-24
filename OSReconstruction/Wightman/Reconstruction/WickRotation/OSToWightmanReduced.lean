/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison

/-!
# Reduced-coordinate support for the selected OS witness

This file contains small reduced-coordinate facts for the selected analytic
witness `bvt_F OS lgc`.  The point is purely algebraic: because the selected
witness is invariant under common complex translations, it factors through
successive differences.
-/

open scoped Classical NNReal
open BigOperators
open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The canonical reduced imaginary direction: every reduced difference slot
uses the fixed future-timelike safe basepoint vector. -/
def canonicalReducedDirection (m : ℕ) : Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

/-- Complex-valued version of `canonicalReducedDirection`. -/
def canonicalReducedDirectionC (m : ℕ) : BHW.ReducedNPointConfig d m :=
  fun k μ => (canonicalReducedDirection (d := d) m k μ : ℂ)

/-- The canonical reduced direction lies in the product forward cone. -/
theorem canonicalReducedDirection_mem_productForwardConeReal
    (m : ℕ) :
    canonicalReducedDirection (d := d) m ∈ BHW.ProductForwardConeReal d m := by
  intro _k
  exact BHW.safeBasepointVec_mem_forwardCone (d := d)

/-- Positive imaginary height in the canonical reduced direction lies in the
reduced forward tube. -/
theorem reducedCanonicalApproach_mem_reducedForwardTube
    (m : ℕ) (ξ : NPointDomain d m) {ε : ℝ} (hε : 0 < ε) :
    (fun k μ =>
      (ξ k μ : ℂ) + ε * canonicalReducedDirectionC (d := d) m k μ *
        Complex.I) ∈ BHW.ReducedForwardTubeN d m := by
  intro k
  have hbhw :
      BHW.InOpenForwardCone d (ε • BHW.safeBasepointVec d) :=
    BHW.inOpenForwardCone_smul_pos
      (BHW.safeBasepointVec_mem_forwardCone (d := d)) hε
  have hcone :
      BHW.InOpenForwardCone d
        (ε • canonicalReducedDirection (d := d) m k) := by
    simpa [canonicalReducedDirection] using hbhw
  convert hcone using 1
  funext μ
  simp [canonicalReducedDirectionC, canonicalReducedDirection, Pi.smul_apply,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- The reduced forward tube is contained in the reduced permuted extended
tube.  The proof uses the public safe section to lift reduced coordinates to
the absolute forward tube and then projects back. -/
theorem reducedForwardTubeN_subset_reducedPermutedExtendedTubeN
    (m : ℕ) :
    BHW.ReducedForwardTubeN d m ⊆
      BHW.ReducedPermutedExtendedTubeN d m := by
  intro η hη
  refine ⟨BHW.safeSection d m η, ?_, ?_⟩
  · exact BHW.forwardTube_subset_permutedExtendedTube
      (BHW.safeSection_mem_forwardTube (d := d) m η hη)
  · exact BHW.reducedDiffMap_safeSection (d := d) (m := m) η

omit [NeZero d] in
/-- The reduced PET is open.  This uses the zero-basepoint reduced section as a
local lift of the quotient map `reducedDiffMap`: an absolute PET neighborhood of
a lift projects to a reduced PET neighborhood. -/
theorem isOpen_reducedPermutedExtendedTubeN
    (m : ℕ) :
    IsOpen (BHW.ReducedPermutedExtendedTubeN d m) := by
  rw [isOpen_iff_mem_nhds]
  intro η hη
  rw [BHW.ReducedPermutedExtendedTubeN, BHW.reducedPermutedExtendedTube] at hη ⊢
  rcases hη with ⟨z, hzPET, hzred⟩
  let Φ : BHW.ReducedNPointConfig d m →
      (Fin (m + 1) → Fin (d + 1) → ℂ) :=
    fun η' => z + BHW.reducedDiffSection (m + 1) d (η' - η)
  have hΦ_cont : Continuous Φ := by
    have hsub : Continuous (fun η' : BHW.ReducedNPointConfig d m => η' - η) :=
      continuous_id.sub continuous_const
    exact continuous_const.add
      ((BHW.reducedDiffSection (m + 1) d).continuous.comp hsub)
  have hΦη : Φ η = z := by
    have hzero :
        (BHW.reducedDiffSection (m + 1) d
          (0 : BHW.ReducedNPointConfig d m)) = 0 := by
      exact map_zero (BHW.reducedDiffSection (m + 1) d)
    ext k μ
    change (z + BHW.reducedDiffSection (m + 1) d (η - η)) k μ = z k μ
    rw [sub_self, hzero]
    simp
  have hPET_nhds : BHW.PermutedExtendedTube d (m + 1) ∈ nhds z :=
    BHW.isOpen_permutedExtendedTube.mem_nhds hzPET
  have hpre :
      Φ ⁻¹' BHW.PermutedExtendedTube d (m + 1) ∈ nhds η := by
    have htendsto : Filter.Tendsto Φ (nhds η) (nhds z) := by
      simpa [hΦη] using hΦ_cont.tendsto η
    exact htendsto hPET_nhds
  refine Filter.mem_of_superset hpre ?_
  intro η' hη'
  refine ⟨Φ η', hη', ?_⟩
  calc
    BHW.reducedDiffMap (m + 1) d (Φ η')
        =
      BHW.reducedDiffMap (m + 1) d z +
        BHW.reducedDiffMap (m + 1) d
          (BHW.reducedDiffSection (m + 1) d (η' - η)) := by
          change
            BHW.reducedDiffMap (m + 1) d
                (z + BHW.reducedDiffSection (m + 1) d (η' - η)) =
              BHW.reducedDiffMap (m + 1) d z +
                BHW.reducedDiffMap (m + 1) d
                  (BHW.reducedDiffSection (m + 1) d (η' - η))
          exact map_add (BHW.reducedDiffMap (m + 1) d) z
            (BHW.reducedDiffSection (m + 1) d (η' - η))
    _ = η + (η' - η) := by
          rw [hzred, BHW.reducedDiffMap_section]
    _ = η' := by
          ext k μ
          simp

omit [NeZero d] in
/-- A reduced configuration lies in the reduced forward tube exactly when its
imaginary part lies in the product forward cone.  This form is useful for
pulled-sector boundary approaches, where the real part has first been moved by
the induced reduced permutation. -/
theorem reducedForwardTubeN_of_im_mem_productForwardConeReal
    (m : ℕ) (ζ : BHW.ReducedNPointConfig d m)
    (hζ : (fun k μ => (ζ k μ).im) ∈ BHW.ProductForwardConeReal d m) :
    ζ ∈ BHW.ReducedForwardTubeN d m := by
  simpa [BHW.ReducedForwardTubeN, BHW.ReducedForwardTube,
    BHW.ReducedForwardCone, BHW.ProductForwardCone] using hζ

/-- Canonical reduced direction after applying an absolute permutation through
the induced reduced-difference action. -/
noncomputable def permutedCanonicalReducedDirectionC
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.ReducedNPointConfig d m :=
  BHW.permOnReducedDiff (d := d) (n := m + 1) σ
    (canonicalReducedDirectionC (d := d) m)

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

/-- Canonical finite shell used in the boundary-value approach. -/
def canonicalShell
    (n : ℕ) (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    (x k μ : ℂ) +
      ε * (canonicalForwardConeDirection (d := d) n k μ : ℂ) * Complex.I

/-- Canonical shell with the imaginary direction reindexed by an absolute
permutation. -/
def permutedEtaCanonicalShellOfPerm
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : NPointDomain d n) (ε : ℝ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    (x k μ : ℂ) +
      ε * (canonicalForwardConeDirection (d := d) n (σ k) μ : ℂ) * Complex.I

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

omit [NeZero d] in
/-- Absolute selected pair difference as a continuous linear map. -/
noncomputable def absolutePairDiffCLM
    (n : ℕ) (i j : Fin n) :
    NPointDomain d n →L[ℝ] (Fin (d + 1) → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
      (φ := fun _ => Fin (d + 1) → ℝ) j) -
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
      (φ := fun _ => Fin (d + 1) → ℝ) i)

omit [NeZero d] in
@[simp] theorem absolutePairDiffCLM_apply
    (n : ℕ) (i j : Fin n) (x : NPointDomain d n) :
    absolutePairDiffCLM (d := d) n i j x =
      fun μ => x j μ - x i μ := by
  rfl

/-- Composing the selected reduced pair-difference map with successive real
differences is the ordinary absolute selected pair difference. -/
theorem reducedPairDiffCLM_comp_reducedDiffMapRealCLM
    (m : ℕ) (i j : Fin (m + 1)) :
    (reducedPairDiffCLM (d := d) m i j).comp
        (BHW.reducedDiffMapRealCLM (m + 1) d) =
      absolutePairDiffCLM (d := d) (m + 1) i j := by
  ext x μ
  change
    reducedPairDiffCLM (d := d) m i j
        (BHW.reducedDiffMapReal (m + 1) d x) μ =
      x j μ - x i μ
  rw [reducedPairDiffCLM_apply]
  exact congrFun (reducedPairDiff_reducedDiffMapReal (d := d) m i j x) μ

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

private theorem continuous_prependBasepointReal_zero
    (m : ℕ) :
    Continuous (fun ξ : NPointDomain d m =>
      BHW.prependBasepointReal d m 0 ξ) := by
  have _ : NeZero d := inferInstance
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  by_cases hk : k.val = 0
  · have h :
        (fun ξ : NPointDomain d m =>
          BHW.prependBasepointReal d m 0 ξ k μ) =
        fun _ => (0 : SpacetimeDim d) μ := by
        funext ξ
        simp [BHW.prependBasepointReal, hk]
    rw [h]
    exact continuous_const
  · have h :
        (fun ξ : NPointDomain d m =>
          BHW.prependBasepointReal d m 0 ξ k μ) =
        fun ξ => ξ (⟨k.val - 1, by omega⟩ : Fin m) μ := by
        funext ξ
        simp [BHW.prependBasepointReal, hk]
    rw [h]
    exact (continuous_apply μ).comp
      (continuous_apply (⟨k.val - 1, by omega⟩ : Fin m))

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
theorem replaceReducedCoord_selected
    (m : ℕ) (q : Fin m) (ξ : NPointDomain d m)
    (v : Fin (d + 1) → ℝ) :
    replaceReducedCoord (d := d) m q ξ v q = v := by
  simp [replaceReducedCoord]

omit [NeZero d] in
theorem replaceReducedCoord_off
    (m : ℕ) {q r : Fin m} (hqr : r ≠ q)
    (ξ : NPointDomain d m) (v : Fin (d + 1) → ℝ) :
    replaceReducedCoord (d := d) m q ξ v r = ξ r := by
  simp [replaceReducedCoord, hqr]

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

omit [NeZero d] in
/-- Replacing the adjacent selected reduced coordinate by a spacelike vector
lands on the adjacent reduced spacelike edge. -/
theorem replaceReducedCoord_mem_adjacent_edge_of_spacelike
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) (v : Fin (d + 1) → ℝ)
    (hv : MinkowskiSpace.IsSpacelike d v) :
    replaceReducedCoord (d := d) m ⟨i.val, by omega⟩ ξ v ∈
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  rw [mem_reducedSpacelikeSwapEdge_adjacent_iff]
  simpa [replaceReducedCoord] using hv

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

/-- The canonical absolute forward-cone direction descends to the canonical
reduced direction. -/
theorem canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC
    (m : ℕ) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) k μ : ℂ)) =
      canonicalReducedDirectionC (d := d) m := by
  have _ : NeZero d := inferInstance
  ext j μ
  rw [BHW.reducedDiffMap_apply]
  by_cases hμ : μ = 0
  · subst μ
    simp [BHW.diffCoordEquiv_apply, canonicalForwardConeDirection, canonicalReducedDirectionC,
      canonicalReducedDirection, BHW.safeBasepointVec]
  · simp [BHW.diffCoordEquiv_apply, canonicalForwardConeDirection, canonicalReducedDirectionC,
      canonicalReducedDirection, BHW.safeBasepointVec, hμ]

/-- The permuted canonical absolute direction descends to the induced reduced
permutation of the canonical reduced direction. -/
theorem permutedCanonicalForwardDirection_reducedDiff_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.reducedDiffMap (m + 1) d
        (fun k μ =>
          (canonicalForwardConeDirection (d := d) (m + 1) (σ k) μ : ℂ)) =
      permutedCanonicalReducedDirectionC (d := d) m σ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let η : Fin (m + 1) → Fin (d + 1) → ℂ :=
    fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) k μ : ℂ)
  calc
    BHW.reducedDiffMap (m + 1) d
        (fun k μ =>
          (canonicalForwardConeDirection (d := d) (m + 1) (σ k) μ : ℂ))
        = BHW.reducedDiffMap (m + 1) d (fun k => η (σ k)) := by
            rfl
    _ = BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d η) := by
            exact (BHW.permOnReducedDiff_reducedDiffMap
              (d := d) (n := m + 1) σ η).symm
    _ = permutedCanonicalReducedDirectionC (d := d) m σ := by
            rw [canonicalForwardConeDirection_reducedDiff_eq_canonicalReducedDirectionC]
            rfl

/-- The reduced coordinates of the canonical shell split into the reduced real
basepoint and the canonical reduced imaginary direction. -/
theorem reducedDiffMap_canonicalShell_eq
    (m : ℕ) (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (canonicalShell (d := d) (m + 1) x ε) =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  have _ : NeZero d := inferInstance
  ext j μ
  rw [BHW.reducedDiffMap_apply]
  by_cases hμ : μ = 0
  · subst μ
    rw [BHW.reducedDiffMapReal_apply]
    simp [BHW.diffCoordEquiv_apply, canonicalShell,
      canonicalForwardConeDirection, canonicalReducedDirectionC,
      canonicalReducedDirection, BHW.safeBasepointVec]
    ring_nf
  · rw [BHW.reducedDiffMapReal_apply]
    simp [BHW.diffCoordEquiv_apply, canonicalShell,
      canonicalForwardConeDirection, canonicalReducedDirectionC,
      canonicalReducedDirection, BHW.safeBasepointVec, hμ]

/-- The reduced coordinates of the permuted-eta canonical shell split into the
same reduced real basepoint and the permuted canonical reduced direction. -/
theorem reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x : NPointDomain d (m + 1)) (ε : ℝ) :
    BHW.reducedDiffMap (m + 1) d
        (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε) =
      fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
          ε * permutedCanonicalReducedDirectionC (d := d) m σ k μ * Complex.I := by
  ext j μ
  rw [BHW.reducedDiffMap_apply]
  have hdir :=
    congrFun
      (congrFun
        (permutedCanonicalForwardDirection_reducedDiff_eq
          (d := d) m σ) j) μ
  rw [BHW.reducedDiffMap_apply] at hdir
  rw [BHW.diffCoordEquiv_apply]
  rw [BHW.reducedDiffMapReal_apply]
  rw [← hdir]
  rw [BHW.diffCoordEquiv_apply]
  simp [permutedEtaCanonicalShellOfPerm]
  ring_nf

/-- The selected OS analytic witness descended to reduced difference
coordinates through the public safe section. -/
def bvt_F_reduced
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) : BHW.ReducedNPointConfig d m → ℂ :=
  fun η => bvt_F OS lgc (m + 1) (BHW.safeSection d m η)

private theorem safeSection_differentiable
    (m : ℕ) :
    Differentiable ℂ (fun η : BHW.ReducedNPointConfig d m =>
      BHW.safeSection d m η) := by
  have _ : NeZero d := inferInstance
  change Differentiable ℂ
    (fun η : BHW.ReducedNPointConfig d m =>
      (BHW.reducedDiffSection (m + 1) d) η + BHW.safeUniformShift d m)
  have hconst : Differentiable ℂ
      (fun _ : BHW.ReducedNPointConfig d m => BHW.safeUniformShift d m) := by
    exact differentiable_const _
  exact (BHW.reducedDiffSection (m + 1) d).differentiable.add hconst

/-- The reduced selected witness is holomorphic on the reduced forward tube. -/
theorem bvt_F_reduced_holomorphicOn_reducedForwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    DifferentiableOn ℂ (bvt_F_reduced (d := d) OS lgc m)
      (BHW.ReducedForwardTubeN d m) := by
  have hsec :
      DifferentiableOn ℂ
        (fun η : BHW.ReducedNPointConfig d m => BHW.safeSection d m η)
        (BHW.ReducedForwardTubeN d m) :=
    (safeSection_differentiable (d := d) m).differentiableOn
  have hcomp :
      DifferentiableOn ℂ
        (fun η : BHW.ReducedNPointConfig d m =>
          bvt_F OS lgc (m + 1) (BHW.safeSection d m η))
        (BHW.ReducedForwardTubeN d m) := by
    refine DifferentiableOn.comp (bvt_F_holomorphic OS lgc (m + 1)) hsec ?_
    intro η hη
    simpa [BHW_forwardTube_eq (d := d) (n := m + 1)] using
      BHW.safeSection_mem_forwardTube (d := d) m η hη
  simpa [bvt_F_reduced] using hcomp

/-- The reduced selected witness is holomorphic after pulling the reduced
forward tube back along the selected swap action. -/
theorem bvt_F_reduced_holomorphicOn_swapPulledForwardTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    DifferentiableOn ℂ
      (fun ζ : BHW.ReducedNPointConfig d m =>
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ))
      {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m} := by
  have hperm_global :
      Differentiable ℂ
        (fun ζ : BHW.ReducedNPointConfig d m =>
          BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ) :=
    ContinuousLinearMap.differentiable
      (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j))
  have hperm :
      DifferentiableOn ℂ
        (fun ζ : BHW.ReducedNPointConfig d m =>
          BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ)
        {ζ | BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} :=
    hperm_global.differentiableOn
  exact
    (bvt_F_reduced_holomorphicOn_reducedForwardTube (d := d) OS lgc m).comp
      hperm (fun ζ hζ => hζ)

/-- The selected OS analytic witness factors through reduced difference
coordinates.  This is the theorem-2 reduced-coordinate entry point: no locality
or BHW PET uniqueness is used, only common complex translation invariance of the
chosen OS witness. -/
theorem bvt_F_eq_bvt_F_reduced_reducedDiffMap
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) :
    bvt_F OS lgc (m + 1) z =
      bvt_F_reduced (d := d) OS lgc m
        (BHW.reducedDiffMap (m + 1) d z) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let s : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.safeSection d m (BHW.reducedDiffMap (m + 1) d z)
  have hred :
      BHW.reducedDiffMap (m + 1) d z =
        BHW.reducedDiffMap (m + 1) d s := by
    simpa [s] using
      (BHW.reducedDiffMap_safeSection (d := d) (m := m)
        (BHW.reducedDiffMap (m + 1) d z)).symm
  obtain ⟨c, hc⟩ :=
    BHW.exists_uniformShift_eq_of_reducedDiffMap_eq
      (d := d) z s hred
  have hshift :
      bvt_F OS lgc (m + 1) s = bvt_F OS lgc (m + 1) z := by
    rw [hc]
    exact bvt_F_translationInvariant OS lgc (m + 1) z c
  simpa [bvt_F_reduced, s] using hshift.symm

/-- The reduced canonical positive-height approach is exactly the full
canonical shell after factorization through successive differences. -/
theorem bvt_F_reduced_canonicalApproach_eq_bvt_F_canonicalShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (x : NPointDomain d (m + 1)) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) =
      bvt_F OS lgc (m + 1)
        (canonicalShell (d := d) (m + 1) x ε) := by
  have hfac :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m
      (canonicalShell (d := d) (m + 1) x ε)
  have hred := reducedDiffMap_canonicalShell_eq (d := d) m x ε
  rw [← hred]
  exact hfac.symm

/-- The reduced swapped positive-height approach is the full canonical shell
after swapping the real variables.  This is the finite-height transport packet
behind the reduced two-direction DCT step. -/
theorem bvt_F_reduced_permutedApproach_eq_bvt_F_swappedCanonicalShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (x : NPointDomain d (m + 1)) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) =
      bvt_F OS lgc (m + 1)
        (canonicalShell (d := d) (m + 1)
          (fun k => x (Equiv.swap i j k)) ε) := by
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  have hfac :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m
      (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε)
  have hred :=
    reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
      (d := d) m σ x ε
  have hto_permuted :
      bvt_F_reduced (d := d) OS lgc m
          (fun k μ =>
            (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC
                  (d := d) m (Equiv.swap i j) k μ *
                Complex.I) =
        bvt_F OS lgc (m + 1)
          (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε) := by
    rw [← hred]
    exact hfac.symm
  have hperm :=
    bvt_F_perm (d := d) OS lgc (m + 1) σ
      (canonicalShell (d := d) (m + 1)
        (fun k => x (σ k)) ε)
  have hpermuted_to_canonical :
      bvt_F OS lgc (m + 1)
          (permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε) =
        bvt_F OS lgc (m + 1)
          (canonicalShell (d := d) (m + 1)
            (fun k => x (σ k)) ε) := by
    have hcfg :
        (fun k =>
          canonicalShell (d := d) (m + 1)
            (fun l => x (σ l)) ε (σ k)) =
          permutedEtaCanonicalShellOfPerm (d := d) (m + 1) σ x ε := by
      ext k μ
      simp [σ, canonicalShell, permutedEtaCanonicalShellOfPerm]
    rw [← hcfg]
    exact hperm
  exact hto_permuted.trans hpermuted_to_canonical

/-- Integral form of the finite-height reduced transport packet: the reduced
two-direction branch difference is the difference of two ordinary canonical
forward-shell integrals, with the left real variables swapped. -/
theorem bvt_F_reduced_two_direction_integral_eq_swappedCanonicalShell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : NPointDomain d (m + 1) → ℂ) (ε : ℝ) :
    ((∫ x : NPointDomain d (m + 1),
        bvt_F_reduced (d := d) OS lgc m
          (fun k μ =>
            (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC
                  (d := d) m (Equiv.swap i j) k μ *
                Complex.I) *
          φ x) -
      (∫ x : NPointDomain d (m + 1),
        bvt_F_reduced (d := d) OS lgc m
          (fun k μ =>
            (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) m k μ *
                Complex.I) *
          φ x)) =
    ((∫ x : NPointDomain d (m + 1),
        bvt_F OS lgc (m + 1)
          (canonicalShell (d := d) (m + 1)
            (fun k => x (Equiv.swap i j k)) ε) *
          φ x) -
      (∫ x : NPointDomain d (m + 1),
        bvt_F OS lgc (m + 1)
          (canonicalShell (d := d) (m + 1) x ε) *
          φ x)) := by
  congr 1
  · refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      change
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            φ x =
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1)
              (fun k => x (Equiv.swap i j k)) ε) *
            φ x
      rw [bvt_F_reduced_permutedApproach_eq_bvt_F_swappedCanonicalShell
        (d := d) OS lgc m i j x ε]
  · refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      change
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            φ x =
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε) *
            φ x
      rw [bvt_F_reduced_canonicalApproach_eq_bvt_F_canonicalShell
        (d := d) OS lgc m x ε]

/-- Uniform polynomial-growth bound for the selected witness on canonical
positive-height shells with `0 < ε ≤ 1`.

The bound is independent of the height.  This is the quantitative input needed
for the reduced two-direction dominated-convergence packet. -/
private theorem bvt_F_canonicalShell_uniform_growth_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hgrowth :
      ∀ z, z ∈ ForwardTube d n →
        ‖bvt_F OS lgc n z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (x : NPointDomain d n) {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) :
    ‖bvt_F OS lgc n (canonicalShell (d := d) n x ε)‖ ≤
      (C_bd *
          (1 +
            ‖(fun k μ =>
              (canonicalForwardConeDirection (d := d) n k μ : ℂ) *
                Complex.I)‖) ^ N) *
        (1 + ‖x‖) ^ N := by
  let shift1 : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => (canonicalForwardConeDirection (d := d) n k μ : ℂ) * Complex.I
  let shiftε : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => (ε : ℂ) *
      (canonicalForwardConeDirection (d := d) n k μ : ℂ) * Complex.I
  let xC : Fin n → Fin (d + 1) → ℂ := fun k μ => (x k μ : ℂ)
  have hzFT : canonicalShell (d := d) n x ε ∈ ForwardTube d n := by
    rw [forwardTube_eq_imPreimage, Set.mem_setOf_eq]
    have hη_abs :
        canonicalForwardConeDirection (d := d) n ∈ ForwardConeAbs d n :=
      (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n)
        (canonicalForwardConeDirection (d := d) n)).1
        (canonicalForwardConeDirection_mem (d := d) n)
    have hy :=
      forwardConeAbs_smul d n ε hε
        (canonicalForwardConeDirection (d := d) n) hη_abs
    convert hy using 1
    ext k μ
    simp [canonicalShell, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hxC_norm : ‖xC‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
    intro k
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
    intro μ
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (norm_le_pi_norm (x k) μ).trans (norm_le_pi_norm x k)
  have hshift_eq : shiftε = (ε : ℂ) • shift1 := by
    ext k μ
    simp [shiftε, shift1, Pi.smul_apply]
    ring
  have hε_norm : ‖(ε : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε)]
    exact hε_le
  have hshift_norm : ‖shiftε‖ ≤ ‖shift1‖ := by
    rw [hshift_eq, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hε_norm
  have hshell_norm :
      ‖canonicalShell (d := d) n x ε‖ ≤ ‖x‖ + ‖shift1‖ := by
    calc
      ‖canonicalShell (d := d) n x ε‖
          ≤ ‖xC‖ + ‖shiftε‖ := by
            simpa [canonicalShell, xC, shiftε] using norm_add_le xC shiftε
      _ ≤ ‖x‖ + ‖shift1‖ := add_le_add hxC_norm hshift_norm
  have hshell_growth :
      1 + ‖canonicalShell (d := d) n x ε‖ ≤
        (1 + ‖shift1‖) * (1 + ‖x‖) := by
    have hstep :
        1 + ‖canonicalShell (d := d) n x ε‖ ≤
          1 + (‖x‖ + ‖shift1‖) := by
      linarith
    have hprod : 1 + (‖x‖ + ‖shift1‖) ≤
        (1 + ‖shift1‖) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg x, norm_nonneg shift1]
    exact hstep.trans hprod
  calc
    ‖bvt_F OS lgc n (canonicalShell (d := d) n x ε)‖
        ≤ C_bd * (1 + ‖canonicalShell (d := d) n x ε‖) ^ N :=
          hgrowth _ hzFT
    _ ≤ C_bd * ((1 + ‖shift1‖) * (1 + ‖x‖)) ^ N := by
          gcongr
    _ = (C_bd * (1 + ‖shift1‖) ^ N) * (1 + ‖x‖) ^ N := by
          rw [mul_pow]
          ring

/-- Uniform integrable domination for the reduced two-direction branch
difference on small positive heights.

This discharges the domination half of the reduced locality DCT from the
global forward-tube polynomial growth of the selected analytic witness.  The
pointwise Ruelle/Jost boundary equality remains a separate input. -/
theorem bvt_F_reduced_two_direction_difference_bound_eventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d (m + 1)) :
    ∃ bound : NPointDomain d (m + 1) → ℝ,
      Integrable bound volume ∧
        ∀ᶠ (ε : ℝ) in
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
          ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
            ‖(bvt_F_reduced (d := d) OS lgc m
                  (fun k μ =>
                    (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                      ε *
                        permutedCanonicalReducedDirectionC
                          (d := d) m (Equiv.swap i j) k μ *
                        Complex.I) -
                bvt_F_reduced (d := d) OS lgc m
                  (fun k μ =>
                    (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                      ε * canonicalReducedDirectionC (d := d) m k μ *
                        Complex.I)) *
                φ x‖ ≤ bound x := by
  rcases (full_analytic_continuation_with_acr_symmetry_growth
      OS lgc (m + 1)).choose_spec with
    ⟨_hACR, _hFT, _hF_euclid, _hF_perm, _hF_trans,
      _hNegCanonical, hGrowth⟩
  obtain ⟨C_bd, N, hC, hgrowth⟩ := hGrowth
  let shift1 : Fin (m + 1) → Fin (d + 1) → ℂ :=
    fun k μ => (canonicalForwardConeDirection (d := d) (m + 1) k μ : ℂ) *
      Complex.I
  let Cshell : ℝ := C_bd * (1 + ‖shift1‖) ^ N
  let coeff : ℝ := 2 * Cshell * 2 ^ (N - 1)
  let bound : NPointDomain d (m + 1) → ℝ :=
    fun x => coeff * (‖φ x‖ + ‖x‖ ^ N * ‖φ x‖)
  have hCshell_nonneg : 0 ≤ Cshell := by
    exact mul_nonneg (le_of_lt hC) (pow_nonneg (by positivity) N)
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hbound_integrable : Integrable bound volume := by
    haveI : MeasureTheory.Measure.IsAddHaarMeasure
        (volume : Measure (NPointDomain d (m + 1))) :=
      MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
    haveI : (volume : Measure (NPointDomain d (m + 1))).HasTemperateGrowth :=
      inferInstance
    have hf_int := φ.integrable (μ := volume)
    have hpow_int := SchwartzMap.integrable_pow_mul volume φ N
    exact (hf_int.norm.add hpow_int).const_mul coeff
  refine ⟨bound, hbound_integrable, ?_⟩
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  have hlt_one : ∀ᶠ ε : ℝ in l, ε < 1 := by
    have hmem : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
      isOpen_Iio.mem_nhds (by norm_num)
    exact nhdsWithin_le_nhds hmem
  have hsmall : ∀ᶠ ε : ℝ in l, 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, hlt_one] with ε hε_pos hε_lt
    exact ⟨hε_pos, le_of_lt hε_lt⟩
  filter_upwards [hsmall] with ε hε_small
  refine Filter.Eventually.of_forall ?_
  intro x
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let xσ : NPointDomain d (m + 1) := fun k => x (σ k)
  have hxσ_norm : ‖xσ‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
    intro k
    exact norm_le_pi_norm x (σ k)
  have hcan_branch :
      ‖bvt_F OS lgc (m + 1)
          (canonicalShell (d := d) (m + 1) x ε)‖ ≤
        Cshell * (1 + ‖x‖) ^ N := by
    simpa [Cshell, shift1] using
      bvt_F_canonicalShell_uniform_growth_bound
        (d := d) OS lgc (m + 1) C_bd N hC hgrowth
        x hε_small.1 hε_small.2
  have hperm_branch :
      ‖bvt_F OS lgc (m + 1)
          (canonicalShell (d := d) (m + 1) xσ ε)‖ ≤
        Cshell * (1 + ‖x‖) ^ N := by
    have hraw :
        ‖bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) xσ ε)‖ ≤
          Cshell * (1 + ‖xσ‖) ^ N := by
      simpa [Cshell, shift1] using
        bvt_F_canonicalShell_uniform_growth_bound
          (d := d) OS lgc (m + 1) C_bd N hC hgrowth
          xσ hε_small.1 hε_small.2
    have hpow :
        (1 + ‖xσ‖) ^ N ≤ (1 + ‖x‖) ^ N := by
      gcongr
    exact hraw.trans (mul_le_mul_of_nonneg_left hpow hCshell_nonneg)
  have hvals :
      ‖bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) xσ ε) -
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε)‖ ≤
        2 * Cshell * (1 + ‖x‖) ^ N := by
    calc
      ‖bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) xσ ε) -
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε)‖
          ≤
        ‖bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) xσ ε)‖ +
          ‖bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε)‖ := norm_sub_le _ _
      _ ≤ Cshell * (1 + ‖x‖) ^ N +
          Cshell * (1 + ‖x‖) ^ N := add_le_add hperm_branch hcan_branch
      _ = 2 * Cshell * (1 + ‖x‖) ^ N := by ring
  have hdiff :
      ‖(bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I)) *
          φ x‖ ≤
        (2 * Cshell * (1 + ‖x‖) ^ N) * ‖φ x‖ := by
    rw [bvt_F_reduced_permutedApproach_eq_bvt_F_swappedCanonicalShell
        (d := d) OS lgc m i j x ε,
      bvt_F_reduced_canonicalApproach_eq_bvt_F_canonicalShell
        (d := d) OS lgc m x ε]
    change
      ‖(bvt_F OS lgc (m + 1)
              (canonicalShell (d := d) (m + 1) xσ ε) -
            bvt_F OS lgc (m + 1)
              (canonicalShell (d := d) (m + 1) x ε)) *
          φ x‖ ≤
        (2 * Cshell * (1 + ‖x‖) ^ N) * ‖φ x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hvals (norm_nonneg _)
  have hpoly :
      (1 + ‖x‖) ^ N ≤ 2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N) :=
    add_pow_le (by positivity) (norm_nonneg x) N
  have hdom :
      (2 * Cshell * (1 + ‖x‖) ^ N) * ‖φ x‖ ≤ bound x := by
    have hleft_nonneg : 0 ≤ 2 * Cshell := by positivity
    have hstep :
        2 * Cshell * (1 + ‖x‖) ^ N ≤
          2 * Cshell * (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) :=
      mul_le_mul_of_nonneg_left hpoly hleft_nonneg
    have hstep_mul :
        (2 * Cshell * (1 + ‖x‖) ^ N) * ‖φ x‖ ≤
          (2 * Cshell * (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N))) *
            ‖φ x‖ :=
      mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    calc
      (2 * Cshell * (1 + ‖x‖) ^ N) * ‖φ x‖
          ≤ (2 * Cshell * (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N))) *
              ‖φ x‖ := hstep_mul
      _ = bound x := by
          simp [bound, coeff]
          ring
  exact hdiff.trans hdom

/-- The canonical reduced positive-height integrand is eventually integrable.

The proof transports the reduced integrand to the ordinary canonical
forward-tube shell and then uses the selected witness' polynomial growth
against a Schwartz test. -/
theorem bvt_F_reduced_canonical_integrable_eventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (φ : SchwartzNPoint d (m + 1)) :
    ∀ᶠ (ε : ℝ) in
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            φ x) volume := by
  have hF_growth :
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ z, z ∈ ForwardTube d (m + 1) →
          ‖bvt_F OS lgc (m + 1) z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
    rcases (full_analytic_continuation_with_acr_symmetry_growth
        OS lgc (m + 1)).choose_spec with
      ⟨_hACR, _hFT, _hF_euclid, _hF_perm, _hF_trans,
        _hNegCanonical, hGrowth⟩
    exact hGrowth
  let Wcl : SchwartzNPoint d (m + 1) →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := bvt_W OS lgc (m + 1)
          map_add' := (bvt_W_linear (d := d) OS lgc (m + 1)).map_add
          map_smul' := (bvt_W_linear (d := d) OS lgc (m + 1)).map_smul }
      cont := bvt_W_continuous (d := d) OS lgc (m + 1) }
  have hBV :
      ∃ (W : SchwartzNPoint d (m + 1) →L[ℂ] ℂ),
        ∀ (f : SchwartzNPoint d (m + 1))
          (η : Fin (m + 1) → Fin (d + 1) → ℝ),
          InForwardCone d (m + 1) η →
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                (f x))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (W f)) := by
    refine ⟨Wcl, ?_⟩
    intro f η hη
    simpa [Wcl] using
      bvt_boundary_values (d := d) OS lgc (m + 1) f η hη
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hfull :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε) *
          φ x) volume := by
    simpa [canonicalShell, Complex.ofReal_mul] using
      forward_tube_bv_integrable
        (d := d) (n := m + 1)
        (F := bvt_F OS lgc (m + 1))
        (bvt_F_holomorphic (d := d) OS lgc (m + 1))
        hF_growth hBV φ
        (canonicalForwardConeDirection (d := d) (m + 1))
        (canonicalForwardConeDirection_mem (d := d) (m + 1))
        ε hε
  refine hfull.congr ?_
  filter_upwards with x
  rw [bvt_F_reduced_canonicalApproach_eq_bvt_F_canonicalShell
    (d := d) OS lgc m x ε]

/-- The swapped reduced positive-height integrand is eventually integrable.

The proof first applies canonical integrability to the test function with its
real variables swapped, then transports across the measure-preserving finite
coordinate permutation and the reduced/full branch identity above. -/
theorem bvt_F_reduced_permuted_integrable_eventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d (m + 1)) :
    ∀ᶠ (ε : ℝ) in
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            φ x) volume := by
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let eσ : NPointDomain d (m + 1) ≃L[ℝ] NPointDomain d (m + 1) :=
    (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv
  let φσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eσ φ
  have hcanon :=
    bvt_F_reduced_canonical_integrable_eventually
      (d := d) OS lgc m φσ
  filter_upwards [hcanon] with ε hcanonε
  have hfull :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1) x ε) *
          φσ x) volume := by
    refine hcanonε.congr ?_
    filter_upwards with x
    rw [bvt_F_reduced_canonicalApproach_eq_bvt_F_canonicalShell
      (d := d) OS lgc m x ε]
  have hmp :
      MeasurePreserving
        (fun x : NPointDomain d (m + 1) => fun k => x (σ k))
        (volume : Measure (NPointDomain d (m + 1)))
        (volume : Measure (NPointDomain d (m + 1))) := by
    simpa using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin (m + 1) => Fin (d + 1) → ℝ) σ).symm
  have hcomp :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          (bvt_F OS lgc (m + 1)
            (canonicalShell (d := d) (m + 1)
              (fun k => x (σ k)) ε) *
          φ x)) volume := by
    have hraw := hmp.integrable_comp_of_integrable hfull
    refine hraw.congr ?_
    filter_upwards with x
    simp [φσ, eσ, σ]
  refine hcomp.congr ?_
  filter_upwards with x
  change
    bvt_F OS lgc (m + 1)
        (canonicalShell (d := d) (m + 1)
          (fun k => x (Equiv.swap i j k)) ε) *
        φ x =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) *
        φ x
  rw [bvt_F_reduced_permutedApproach_eq_bvt_F_swappedCanonicalShell
    (d := d) OS lgc m i j x ε]

/-- The reduced two-direction difference integrand is eventually strongly
measurable.  This is a bookkeeping consequence of the two branch integrability
facts above. -/
theorem bvt_F_reduced_two_direction_difference_aestronglyMeasurable_eventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d (m + 1)) :
    ∀ᶠ (ε : ℝ) in
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
      AEStronglyMeasurable
        (fun x : NPointDomain d (m + 1) =>
          (bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) -
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I)) *
            φ x) volume := by
  have hperm :=
    bvt_F_reduced_permuted_integrable_eventually
      (d := d) OS lgc m i j φ
  have hcan :=
    bvt_F_reduced_canonical_integrable_eventually
      (d := d) OS lgc m φ
  filter_upwards [hperm, hcan] with ε hpermε hcanε
  have hdiff_int :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          (bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
            φ x) -
          (bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
            φ x)) volume :=
    hpermε.sub hcanε
  refine hdiff_int.aestronglyMeasurable.congr ?_
  filter_upwards with x
  ring

/-- The reduced selected witness is invariant under the reduced action induced
by an absolute coordinate permutation. -/
theorem bvt_F_reduced_permOnReducedDiff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (ζ : BHW.ReducedNPointConfig d m) :
    bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ) =
      bvt_F_reduced (d := d) OS lgc m ζ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ := BHW.safeSection d m ζ
  let zσ : Fin (m + 1) → Fin (d + 1) → ℂ := fun k => z (σ k)
  have hz_red :
      BHW.reducedDiffMap (m + 1) d z = ζ := by
    simpa [z] using BHW.reducedDiffMap_safeSection (d := d) (m := m) ζ
  have hperm_red :
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ =
        BHW.reducedDiffMap (m + 1) d zσ := by
    calc
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ
          = BHW.permOnReducedDiff (d := d) (n := m + 1) σ
              (BHW.reducedDiffMap (m + 1) d z) := by
                rw [hz_red]
      _ = BHW.reducedDiffMap (m + 1) d zσ := by
            simpa [zσ] using
              BHW.permOnReducedDiff_reducedDiffMap
                (d := d) (n := m + 1) σ z
  have hfac_perm :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m zσ
  have hfac :=
    bvt_F_eq_bvt_F_reduced_reducedDiffMap
      (d := d) OS lgc m z
  calc
    bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ)
        = bvt_F OS lgc (m + 1) zσ := by
            rw [hperm_red]
            exact hfac_perm.symm
    _ = bvt_F OS lgc (m + 1) z := by
            exact bvt_F_perm OS lgc (m + 1) σ z
    _ = bvt_F_reduced (d := d) OS lgc m ζ := by
            rw [← hz_red]
            exact hfac

/-- Boundary equality of the reduced branches on the selected spacelike edge.
The spacelike hypothesis marks the intended edge; the equality itself is the
algebraic reduced permutation invariance of the selected OS witness. -/
theorem bvt_F_reduced_boundary_perm_eq_on_reducedSpacelikeSwapEdge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ∀ ξ ∈ reducedSpacelikeSwapEdge (d := d) m i j,
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ => (ξ k μ : ℂ))) =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ => (ξ k μ : ℂ)) := by
  intro ξ _hξ
  exact bvt_F_reduced_permOnReducedDiff
    (d := d) OS lgc m (Equiv.swap i j)
    (fun k μ => (ξ k μ : ℂ))

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

omit [NeZero d] in
/-- In successive-difference coordinates, swapping adjacent absolute points
adds the selected adjacent difference to the predecessor difference. -/
theorem permOnReducedDiff_adjacentSwap_prev
    (m : ℕ) (i : Fin (m + 1)) (hprev : 0 < i.val)
    (hi : i.val + 1 < m + 1)
    (ζ : BHW.ReducedNPointConfig d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩) ζ
        ⟨i.val - 1, by omega⟩ =
      ζ ⟨i.val - 1, by omega⟩ + ζ ⟨i.val, by omega⟩ := by
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
          ⟨i.val - 1, by omega⟩ μ =
        z ⟨i.val + 1, hi⟩ μ - z ⟨i.val - 1, by omega⟩ μ := by
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnext :
        (⟨(⟨i.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
          Fin (m + 1)) = i := by
      ext
      simp
      omega
    have hcur :
        (⟨(⟨i.val - 1, by omega⟩ : Fin m).val, by omega⟩ :
          Fin (m + 1)) = ⟨i.val - 1, by omega⟩ := by
      ext
      simp
    rw [hnext, hcur]
    have hprev_ne_i :
        (⟨i.val - 1, by omega⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      have hv' : i.val - 1 = i.val := by
        simpa using hv
      omega
    have hprev_ne_next :
        (⟨i.val - 1, by omega⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    rw [Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne hprev_ne_i hprev_ne_next]
  have hζprev :
      ζ ⟨i.val - 1, by omega⟩ μ =
        z i μ - z ⟨i.val - 1, by omega⟩ μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnext :
        (⟨(⟨i.val - 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
          Fin (m + 1)) = i := by
      ext
      simp
      omega
    have hcur :
        (⟨(⟨i.val - 1, by omega⟩ : Fin m).val, by omega⟩ :
          Fin (m + 1)) = ⟨i.val - 1, by omega⟩ := by
      ext
      simp
    rw [hnext, hcur]
  have hζsel :
      ζ ⟨i.val, by omega⟩ μ =
        z ⟨i.val + 1, hi⟩ μ - z i μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ
        ⟨i.val - 1, by omega⟩ μ
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d z) ⟨i.val - 1, by omega⟩ μ := by
          rw [hzred]
    _ =
      BHW.reducedDiffMap (m + 1) d (fun k => z (σ k))
        ⟨i.val - 1, by omega⟩ μ := by
          rw [hperm]
    _ = z ⟨i.val + 1, hi⟩ μ - z ⟨i.val - 1, by omega⟩ μ := hstep
    _ = ζ ⟨i.val - 1, by omega⟩ μ + ζ ⟨i.val, by omega⟩ μ := by
          rw [hζprev, hζsel]
          ring

omit [NeZero d] in
/-- In successive-difference coordinates, swapping adjacent absolute points
adds the selected adjacent difference to the successor difference. -/
theorem permOnReducedDiff_adjacentSwap_next
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (hnext : i.val + 2 < m + 1)
    (ζ : BHW.ReducedNPointConfig d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩) ζ
        ⟨i.val + 1, by omega⟩ =
      ζ ⟨i.val + 1, by omega⟩ + ζ ⟨i.val, by omega⟩ := by
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
          ⟨i.val + 1, by omega⟩ μ =
        z ⟨i.val + 2, hnext⟩ μ - z i μ := by
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnextIdx :
        (⟨(⟨i.val + 1, by omega⟩ : Fin m).val + 1, by omega⟩ :
          Fin (m + 1)) = ⟨i.val + 2, hnext⟩ := by
      ext
      simp
    have hcur :
        (⟨(⟨i.val + 1, by omega⟩ : Fin m).val, by omega⟩ :
          Fin (m + 1)) = ⟨i.val + 1, hi⟩ := by
      ext
      simp
    rw [hnextIdx, hcur]
    have hnext_ne_i :
        (⟨i.val + 2, hnext⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have hnext_ne_next :
        (⟨i.val + 2, hnext⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    rw [Equiv.swap_apply_of_ne_of_ne hnext_ne_i hnext_ne_next]
    rw [Equiv.swap_apply_right]
  have hζnext :
      ζ ⟨i.val + 1, by omega⟩ μ =
        z ⟨i.val + 2, hnext⟩ μ - z ⟨i.val + 1, hi⟩ μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  have hζsel :
      ζ ⟨i.val, by omega⟩ μ =
        z ⟨i.val + 1, hi⟩ μ - z i μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ
        ⟨i.val + 1, by omega⟩ μ
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d z) ⟨i.val + 1, by omega⟩ μ := by
          rw [hzred]
    _ =
      BHW.reducedDiffMap (m + 1) d (fun k => z (σ k))
        ⟨i.val + 1, by omega⟩ μ := by
          rw [hperm]
    _ = z ⟨i.val + 2, hnext⟩ μ - z i μ := hstep
    _ = ζ ⟨i.val + 1, by omega⟩ μ + ζ ⟨i.val, by omega⟩ μ := by
          rw [hζnext, hζsel]
          ring

omit [NeZero d] in
/-- In successive-difference coordinates, swapping adjacent absolute points
leaves every reduced difference strictly to the left of the swapped pair
unchanged. -/
theorem permOnReducedDiff_adjacentSwap_left_far
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (k : Fin m) (hleft : k.val + 1 < i.val)
    (ζ : BHW.ReducedNPointConfig d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩) ζ k =
      ζ k := by
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.reducedDiffSection (m + 1) d ζ
  have hzred : BHW.reducedDiffMap (m + 1) d z = ζ := by
    simpa [z] using BHW.reducedDiffMap_section (m + 1) d ζ
  have hperm :=
    BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z
  ext μ
  have hstep :
      BHW.reducedDiffMap (m + 1) d (fun a => z (σ a)) k μ =
        z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := by
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnext_ne_i :
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hnext_ne_next :
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hcur_ne_i :
        (⟨k.val, by omega⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hcur_ne_next :
        (⟨k.val, by omega⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hnext_ne_i hnext_ne_next]
    rw [Equiv.swap_apply_of_ne_of_ne hcur_ne_i hcur_ne_next]
  have hζ :
      ζ k μ =
        z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ k μ
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d z) k μ := by
          rw [hzred]
    _ =
      BHW.reducedDiffMap (m + 1) d (fun a => z (σ a)) k μ := by
          rw [hperm]
    _ = z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := hstep
    _ = ζ k μ := hζ.symm

omit [NeZero d] in
/-- In successive-difference coordinates, swapping adjacent absolute points
leaves every reduced difference strictly to the right of the swapped pair
unchanged. -/
theorem permOnReducedDiff_adjacentSwap_right_far
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (k : Fin m) (hright : i.val + 1 < k.val)
    (ζ : BHW.ReducedNPointConfig d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩) ζ k =
      ζ k := by
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ :=
    BHW.reducedDiffSection (m + 1) d ζ
  have hzred : BHW.reducedDiffMap (m + 1) d z = ζ := by
    simpa [z] using BHW.reducedDiffMap_section (m + 1) d ζ
  have hperm :=
    BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z
  ext μ
  have hstep :
      BHW.reducedDiffMap (m + 1) d (fun a => z (σ a)) k μ =
        z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := by
    rw [BHW.reducedDiffMap_eq_successive_differences]
    have hnext_ne_i :
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hnext_ne_next :
        (⟨k.val + 1, by omega⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hcur_ne_i :
        (⟨k.val, by omega⟩ : Fin (m + 1)) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hcur_ne_next :
        (⟨k.val, by omega⟩ : Fin (m + 1)) ≠
          ⟨i.val + 1, hi⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hnext_ne_i hnext_ne_next]
    rw [Equiv.swap_apply_of_ne_of_ne hcur_ne_i hcur_ne_next]
  have hζ :
      ζ k μ =
        z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := by
    rw [← hzred]
    rw [BHW.reducedDiffMap_eq_successive_differences]
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ ζ k μ
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (BHW.reducedDiffMap (m + 1) d z) k μ := by
          rw [hzred]
    _ =
      BHW.reducedDiffMap (m + 1) d (fun a => z (σ a)) k μ := by
          rw [hperm]
    _ = z ⟨k.val + 1, by omega⟩ μ -
          z ⟨k.val, by omega⟩ μ := hstep
    _ = ζ k μ := hζ.symm

/-- Applying the same transposition twice to the canonical reduced direction
returns the canonical direction. -/
theorem permOnReducedDiff_swap_permutedCanonicalDirection
    (m : ℕ) (i j : Fin (m + 1)) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j)) =
      canonicalReducedDirectionC (d := d) m := by
  have _ : NeZero d := inferInstance
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  have hmul :=
    BHW.permOnReducedDiff_mul (d := d) (n := m + 1)
      (Equiv.swap i j) (Equiv.swap i j)
      (canonicalReducedDirectionC (d := d) m)
  calc
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j))
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (canonicalReducedDirectionC (d := d) m)) := by
            rfl
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        ((Equiv.swap i j) * (Equiv.swap i j))
        (canonicalReducedDirectionC (d := d) m) := by
            exact hmul.symm
    _ = canonicalReducedDirectionC (d := d) m := by
            simpa using
              BHW.permOnReducedDiff_one (d := d) (n := m + 1)
                (canonicalReducedDirectionC (d := d) m)

/-- The swapped reduced canonical approach is a genuine boundary approach from
the pulled-forward reduced tube: after applying the induced adjacent
transposition, its imaginary part is the positive canonical reduced direction. -/
theorem permutedReducedApproach_mem_swapPulledForwardTube
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    {ε : ℝ} (hε : 0 < ε) :
    (fun k μ =>
      (ξ k μ : ℂ) +
        ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
          Complex.I) ∈
      {ζ : BHW.ReducedNPointConfig d m |
        BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
          BHW.ReducedForwardTubeN d m} := by
  apply reducedForwardTubeN_of_im_mem_productForwardConeReal
  intro k
  have hcone :
      BHW.InOpenForwardCone d
        (ε • canonicalReducedDirection (d := d) m k) := by
    simpa [canonicalReducedDirection] using
      BHW.inOpenForwardCone_smul_pos
        (BHW.safeBasepointVec_mem_forwardCone (d := d)) hε
  convert hcone using 1
  funext μ
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let L : BHW.ReducedNPointConfig d m →L[ℂ] BHW.ReducedNPointConfig d m :=
    BHW.permOnReducedDiff (d := d) (n := m + 1) τ
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  let ητ : BHW.ReducedNPointConfig d m :=
    permutedCanonicalReducedDirectionC (d := d) m τ
  have harg :
      (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) =
        ξC + (ε : ℂ) • (fun k μ => ητ k μ * Complex.I) := by
    ext k μ
    change (ξ k μ : ℂ) + (ε : ℂ) * ητ k μ * Complex.I =
      (ξ k μ : ℂ) + (ε : ℂ) * (ητ k μ * Complex.I)
    ring
  have hLarg :
      L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) =
        L ξC + (ε : ℂ) • L (fun k μ => ητ k μ * Complex.I) := by
    calc
      L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I)
          = L (ξC + (ε : ℂ) • (fun k μ => ητ k μ * Complex.I)) := by
              exact congrArg L harg
      _ = L ξC + (ε : ℂ) • L (fun k μ => ητ k μ * Complex.I) := by
              rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
  have hLi :
      L (fun k μ => ητ k μ * Complex.I) =
        fun k μ => canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
    have hη :
        L ητ = canonicalReducedDirectionC (d := d) m := by
      simpa [L, τ, ητ] using
        permOnReducedDiff_swap_permutedCanonicalDirection (d := d) m i j
    ext k μ
    change L ((fun k μ => ητ k μ * Complex.I)) k μ =
      canonicalReducedDirectionC (d := d) m k μ * Complex.I
    have hmul :
        (fun k μ => ητ k μ * Complex.I) =
          (Complex.I : ℂ) • ητ := by
      ext k μ
      simp [Pi.smul_apply]
      ring
    rw [hmul]
    simp [L, hη, Pi.smul_apply]
    ring
  have hreal0 :
      (L ξC k μ).im = 0 := by
    simpa [L, τ, ξC] using
      permOnReducedDiff_ofReal_im_zero (d := d) m (Equiv.swap i j) ξ k μ
  change (L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) k μ).im =
    (ε • canonicalReducedDirection (d := d) m k) μ
  rw [hLarg, hLi]
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, hreal0, zero_add]
  change ((ε : ℂ) *
      (canonicalReducedDirectionC (d := d) m k μ * Complex.I)).im =
    ε * canonicalReducedDirection (d := d) m k μ
  simp [canonicalReducedDirectionC, canonicalReducedDirection,
    Complex.mul_im, Complex.I_re, Complex.I_im]

/-- Algebraic normal form for the swapped reduced canonical approach: after
applying the induced adjacent transposition, it becomes the canonical reduced
approach based at the permuted real reduced configuration. -/
theorem permOnReducedDiff_permutedReducedApproach_eq_canonical
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m) (ε : ℝ) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
      =
    fun k μ =>
      BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ => (ξ k μ : ℂ)) k μ +
        ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let L : BHW.ReducedNPointConfig d m →L[ℂ] BHW.ReducedNPointConfig d m :=
    BHW.permOnReducedDiff (d := d) (n := m + 1) τ
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  let ητ : BHW.ReducedNPointConfig d m :=
    permutedCanonicalReducedDirectionC (d := d) m τ
  have harg :
      (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) =
        ξC + (ε : ℂ) • (fun k μ => ητ k μ * Complex.I) := by
    ext k μ
    change (ξ k μ : ℂ) + (ε : ℂ) * ητ k μ * Complex.I =
      (ξ k μ : ℂ) + (ε : ℂ) * (ητ k μ * Complex.I)
    ring
  have hmap :
      L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) =
        L ξC + (ε : ℂ) • L (fun k μ => ητ k μ * Complex.I) := by
    calc
      L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I)
          = L (ξC + (ε : ℂ) • (fun k μ => ητ k μ * Complex.I)) := by
              exact congrArg L harg
      _ = L ξC + (ε : ℂ) • L (fun k μ => ητ k μ * Complex.I) := by
              rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
  have hLi :
      L (fun k μ => ητ k μ * Complex.I) =
        fun k μ => canonicalReducedDirectionC (d := d) m k μ * Complex.I := by
    have hη :
        L ητ = canonicalReducedDirectionC (d := d) m := by
      simpa [L, τ, ητ] using
        permOnReducedDiff_swap_permutedCanonicalDirection (d := d) m i j
    ext k μ
    have hmul :
        (fun k μ => ητ k μ * Complex.I) =
          (Complex.I : ℂ) • ητ := by
      ext k μ
      simp
      ring
    rw [hmul]
    simp [L, hη, Pi.smul_apply]
    ring
  ext k μ
  change L (fun k μ => (ξ k μ : ℂ) + ε * ητ k μ * Complex.I) k μ =
    L ξC k μ + ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
  rw [hmap, hLi]
  change L ξC k μ +
      (ε : ℂ) * (canonicalReducedDirectionC (d := d) m k μ * Complex.I) =
    L ξC k μ + (ε : ℂ) * canonicalReducedDirectionC (d := d) m k μ * Complex.I
  ring

/-- The reduced permuted extended tube is stable under the induced absolute
permutation action on successive differences. -/
theorem reducedPermutedExtendedTubeN_permOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    {η : BHW.ReducedNPointConfig d m}
    (hη : η ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    BHW.permOnReducedDiff (d := d) (n := m + 1) σ η ∈
      BHW.ReducedPermutedExtendedTubeN d m := by
  rcases hη with ⟨z, hz, hzred⟩
  have hz_root : z ∈ PermutedExtendedTube d (m + 1) := by
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := m + 1)] using hz
  have hz_perm_root :
      (fun k => z (σ k)) ∈ PermutedExtendedTube d (m + 1) :=
    permutedExtendedTube_perm (d := d) σ hz_root
  have hz_perm :
      (fun k => z (σ k)) ∈ BHW.PermutedExtendedTube d (m + 1) := by
    simpa [BHW_permutedExtendedTube_eq (d := d) (n := m + 1)] using
      hz_perm_root
  refine ⟨fun k => z (σ k), hz_perm, ?_⟩
  rw [← BHW.permOnReducedDiff_reducedDiffMap (d := d) (n := m + 1) σ z]
  rw [hzred]

/-- Inverse form of reduced PET permutation stability. -/
theorem reducedPermutedExtendedTubeN_of_permOnReducedDiff_mem
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    {η : BHW.ReducedNPointConfig d m}
    (hη : BHW.permOnReducedDiff (d := d) (n := m + 1) σ η ∈
      BHW.ReducedPermutedExtendedTubeN d m) :
    η ∈ BHW.ReducedPermutedExtendedTubeN d m := by
  have hback :=
    reducedPermutedExtendedTubeN_permOnReducedDiff
      (d := d) m σ.symm hη
  have hcomp :
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm
          (BHW.permOnReducedDiff (d := d) (n := m + 1) σ η) =
        η := by
    have hmul :=
      BHW.permOnReducedDiff_mul (d := d) (n := m + 1) σ σ.symm η
    rw [← hmul]
    simpa using
      BHW.permOnReducedDiff_one (d := d) (n := m + 1) η
  rw [hcomp] at hback
  exact hback

/-- Positive-height swapped reduced canonical approaches lie in the reduced PET.
The real edge is not asserted to lie in PET; only the regularized point does. -/
theorem permutedReducedApproach_mem_reducedPermutedExtendedTubeN
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    {ε : ℝ} (hε : 0 < ε) :
    (fun k μ =>
      (ξ k μ : ℂ) +
        ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
          Complex.I) ∈ BHW.ReducedPermutedExtendedTubeN d m := by
  let ζ : BHW.ReducedNPointConfig d m := fun k μ =>
    (ξ k μ : ℂ) +
      ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
        Complex.I
  have hafter_forward :
      BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedForwardTubeN d m := by
    simpa [ζ] using
      permutedReducedApproach_mem_swapPulledForwardTube
        (d := d) m i j ξ hε
  have hafter_pet :
      BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j) ζ ∈
        BHW.ReducedPermutedExtendedTubeN d m :=
    reducedForwardTubeN_subset_reducedPermutedExtendedTubeN (d := d) m hafter_forward
  exact
    reducedPermutedExtendedTubeN_of_permOnReducedDiff_mem
      (d := d) m (Equiv.swap i j) hafter_pet

omit [NeZero d] in
/-- Pointwise PET collar for the swapped reduced canonical approach, extracted
from openness of the reduced PET. -/
theorem permutedReducedApproach_eventually_mem_reducedPermutedExtendedTubeN
    (m : ℕ) (i j : Fin (m + 1)) (ξ : NPointDomain d m)
    (hξ_pet :
      (fun k μ => (ξ k μ : ℂ)) ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    ∀ᶠ (ε : ℝ) in
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
            Complex.I) ∈ BHW.ReducedPermutedExtendedTubeN d m := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  let ζperm : ℝ → BHW.ReducedNPointConfig d m := fun ε k μ =>
    (ξ k μ : ℂ) +
      ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
        Complex.I
  have hεC : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (nhds 0) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) l (nhds (0 : ℝ)) := by
      exact Filter.tendsto_id'.2 nhdsWithin_le_nhds
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hid
  have hζperm_tendsto : Filter.Tendsto ζperm l (nhds ξC) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [tendsto_pi_nhds]
    intro μ
    have hterm :
        Filter.Tendsto
          (fun ε : ℝ =>
            (ε : ℂ) *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) l (nhds 0) := by
      simpa [mul_assoc] using
        (hεC.mul_const
          (permutedCanonicalReducedDirectionC
            (d := d) m (Equiv.swap i j) k μ * Complex.I))
    simpa [ζperm, ξC] using (tendsto_const_nhds.add hterm)
  have hS :
      BHW.ReducedPermutedExtendedTubeN d m ∈ nhds ξC :=
    (isOpen_reducedPermutedExtendedTubeN (d := d) m).mem_nhds hξ_pet
  simpa [ζperm, ξC] using hζperm_tendsto hS

/-- Convert a reduced value at the permuted canonical direction into the
corresponding value after applying the induced reduced permutation. -/
theorem bvt_F_reduced_permutedDirection_to_realPermutedCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ξ : NPointDomain d m) (ε : ℝ) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) =
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I)) := by
  exact (bvt_F_reduced_permOnReducedDiff
    (d := d) OS lgc m (Equiv.swap i j)
    (fun k μ =>
      (ξ k μ : ℂ) +
        ε *
          permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
          Complex.I)).symm

/-- Along the canonical reduced forward-tube approach, the selected reduced
witness agrees with any reduced PET extension of it. -/
theorem bvt_F_reduced_canonicalApproach_eq_reducedExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ)
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m) {ε : ℝ} (hε : 0 < ε) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)
      =
    Fred.toFun
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
  have hforward :
      (fun k μ =>
          (ξ k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) ∈
        BHW.ReducedForwardTubeN d m :=
    reducedCanonicalApproach_mem_reducedForwardTube (d := d) m ξ hε
  exact (Fred.agrees_on_reducedForwardTube _ hforward).symm

/-- Along the swapped reduced canonical approach, the selected reduced witness
agrees with any reduced PET extension of it once that approach is known to lie
in the reduced PET.  The proof moves through the induced reduced transposition,
where the approach is in the forward tube. -/
theorem bvt_F_reduced_permutedApproach_eq_reducedExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m) {ε : ℝ} (hε : 0 < ε)
    (hpermuted_domain :
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε *
            permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
            Complex.I) ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
      =
    Fred.toFun
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let ζτ : BHW.ReducedNPointConfig d m :=
    fun k μ =>
      (ξ k μ : ℂ) +
        ε * permutedCanonicalReducedDirectionC (d := d) m τ k μ * Complex.I
  have hforward_after_perm :
      BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ ∈
        BHW.ReducedForwardTubeN d m := by
    simpa [τ, ζτ] using
      permutedReducedApproach_mem_swapPulledForwardTube
        (d := d) m i j ξ hε
  have hdomain_after_perm :
      BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ ∈
        BHW.ReducedPermutedExtendedTubeN d m :=
    reducedForwardTubeN_subset_reducedPermutedExtendedTubeN
      (d := d) m hforward_after_perm
  have hselected_to_perm :
      bvt_F_reduced (d := d) OS lgc m ζτ =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) := by
    simpa [τ, ζτ] using
      bvt_F_reduced_permutedDirection_to_realPermutedCanonical
        (d := d) OS lgc m i j ξ ε
  have hagree_forward :
      Fred.toFun (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) =
        bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) :=
    Fred.agrees_on_reducedForwardTube _ hforward_after_perm
  have hext_perm :
      Fred.toFun (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) =
        Fred.toFun ζτ :=
    Fred.perm_invariant τ ζτ hpermuted_domain hdomain_after_perm
  calc
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
        = bvt_F_reduced (d := d) OS lgc m ζτ := by
            rfl
    _ = bvt_F_reduced (d := d) OS lgc m
          (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) :=
            hselected_to_perm
    _ = Fred.toFun
          (BHW.permOnReducedDiff (d := d) (n := m + 1) τ ζτ) :=
            hagree_forward.symm
    _ = Fred.toFun ζτ := hext_perm
    _ = Fred.toFun
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) := by
            rfl

/-- Positive-height form of
`bvt_F_reduced_permutedApproach_eq_reducedExtension`: the swapped reduced
canonical approach is automatically in the reduced PET for `0 < ε`. -/
theorem bvt_F_reduced_permutedApproach_eq_reducedExtension_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m) {ε : ℝ} (hε : 0 < ε) :
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
      =
    Fred.toFun
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) := by
  exact
    bvt_F_reduced_permutedApproach_eq_reducedExtension
      (d := d) OS lgc m i j Fred ξ hε
      (permutedReducedApproach_mem_reducedPermutedExtendedTubeN
        (d := d) m i j ξ hε)

/-- Pointwise reduced two-direction boundary convergence from a genuine reduced
PET extension and the corresponding PET collar.

This is the non-integral core of the reduced boundary deformation: after both
positive-side approaches have been identified with the same PET extension,
continuity of that extension at the real reduced edge gives the zero limit. -/
theorem bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension_collar
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m)
    (hξ_pet :
      (fun k μ => (ξ k μ : ℂ)) ∈ BHW.ReducedPermutedExtendedTubeN d m)
    (hpermuted_pet :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I) ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  let ζperm : ℝ → BHW.ReducedNPointConfig d m := fun ε k μ =>
    (ξ k μ : ℂ) +
      ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
        Complex.I
  let ζcan : ℝ → BHW.ReducedNPointConfig d m := fun ε k μ =>
    (ξ k μ : ℂ) +
      ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I
  have hpos : ∀ᶠ ε : ℝ in l, 0 < ε := by
    exact self_mem_nhdsWithin
  have hcan_pet : ∀ᶠ ε : ℝ in l, ζcan ε ∈ BHW.ReducedPermutedExtendedTubeN d m := by
    filter_upwards [hpos] with ε hε
    exact reducedForwardTubeN_subset_reducedPermutedExtendedTubeN
      (d := d) m
      (reducedCanonicalApproach_mem_reducedForwardTube (d := d) m ξ hε)
  have hεC : Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) l (nhds 0) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) l (nhds (0 : ℝ)) := by
      exact Filter.tendsto_id'.2 nhdsWithin_le_nhds
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hid
  have hζcan_tendsto : Filter.Tendsto ζcan l (nhds ξC) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [tendsto_pi_nhds]
    intro μ
    have hterm :
        Filter.Tendsto
          (fun ε : ℝ =>
            (ε : ℂ) * canonicalReducedDirectionC (d := d) m k μ *
              Complex.I) l (nhds 0) := by
      simpa [mul_assoc] using
        (hεC.mul_const
          (canonicalReducedDirectionC (d := d) m k μ * Complex.I))
    simpa [ζcan, ξC] using (tendsto_const_nhds.add hterm)
  have hζperm_tendsto : Filter.Tendsto ζperm l (nhds ξC) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [tendsto_pi_nhds]
    intro μ
    have hterm :
        Filter.Tendsto
          (fun ε : ℝ =>
            (ε : ℂ) *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) l (nhds 0) := by
      simpa [mul_assoc] using
        (hεC.mul_const
          (permutedCanonicalReducedDirectionC
            (d := d) m (Equiv.swap i j) k μ * Complex.I))
    simpa [ζperm, ξC] using (tendsto_const_nhds.add hterm)
  have hcan_within :
      Filter.Tendsto ζcan l
        (nhdsWithin ξC (BHW.ReducedPermutedExtendedTubeN d m)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hζcan_tendsto, hcan_pet⟩
  have hperm_within :
      Filter.Tendsto ζperm l
        (nhdsWithin ξC (BHW.ReducedPermutedExtendedTubeN d m)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hζperm_tendsto, hpermuted_pet⟩
  have hFred_cont :
      ContinuousWithinAt Fred.toFun
        (BHW.ReducedPermutedExtendedTubeN d m) ξC :=
    Fred.holomorphic.continuousOn.continuousWithinAt hξ_pet
  have hFred_can :
      Filter.Tendsto (fun ε : ℝ => Fred.toFun (ζcan ε)) l
        (nhds (Fred.toFun ξC)) :=
    hFred_cont.tendsto.comp hcan_within
  have hFred_perm :
      Filter.Tendsto (fun ε : ℝ => Fred.toFun (ζperm ε)) l
        (nhds (Fred.toFun ξC)) :=
    hFred_cont.tendsto.comp hperm_within
  have hselected_to_ext :
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I))
        =ᶠ[l]
      (fun ε : ℝ => Fred.toFun (ζperm ε) - Fred.toFun (ζcan ε)) := by
    filter_upwards [hpos, hpermuted_pet] with ε hε hpet
    have hperm_eq :=
      bvt_F_reduced_permutedApproach_eq_reducedExtension
        (d := d) OS lgc m i j Fred ξ hε hpet
    have hcan_eq :=
      bvt_F_reduced_canonicalApproach_eq_reducedExtension
        (d := d) OS lgc m Fred ξ hε
    change
      bvt_F_reduced (d := d) OS lgc m (ζperm ε) -
          bvt_F_reduced (d := d) OS lgc m (ζcan ε) =
        Fred.toFun (ζperm ε) - Fred.toFun (ζcan ε)
    rw [hperm_eq, hcan_eq]
  refine Filter.Tendsto.congr' hselected_to_ext.symm ?_
  simpa using hFred_perm.sub hFred_can

/-- Pointwise reduced two-direction boundary convergence from a genuine reduced
PET extension.  The required PET collar for the swapped approach is supplied by
openness of the reduced PET. -/
theorem bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (ξ : NPointDomain d m)
    (hξ_pet :
      (fun k μ => (ξ k μ : ℂ)) ∈ BHW.ReducedPermutedExtendedTubeN d m) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) -
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (ξ k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  exact
    bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension_collar
      (d := d) OS lgc m i j Fred ξ hξ_pet
      (permutedReducedApproach_eventually_mem_reducedPermutedExtendedTubeN
        (d := d) m i j ξ hξ_pet)

/-- Integral reduced two-direction boundary convergence from an explicit
pointwise boundary limit and dominated-convergence packet.

This is the DCT core of the reduced locality route.  It deliberately does not
ask for real reduced-PET membership or a reduced extension witness; those are
the analytic/Jost-Ruelle inputs that must supply `hpointwise` and the collar
bound. -/
theorem bvt_F_reduced_two_direction_integral_tendsto_zero_of_pointwise_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : NPointDomain d (m + 1) → ℂ)
    (bound : NPointDomain d (m + 1) → ℝ)
    (hpointwise :
      ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
        Filter.Tendsto
          (fun ε : ℝ =>
            (bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0))
    (hF_meas :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        AEStronglyMeasurable
          (fun x : NPointDomain d (m + 1) =>
            (bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
          ‖(bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x‖ ≤ bound x)
    (hperm_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) volume)
    (hcan_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
              φ x) volume) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              φ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let F : ℝ → NPointDomain d (m + 1) → ℂ := fun ε x =>
    (bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
            ε *
              permutedCanonicalReducedDirectionC
                (d := d) m (Equiv.swap i j) k μ *
              Complex.I) -
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)) *
      φ x
  have hDCT :
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d (m + 1), F ε x)
        l (nhds (∫ x : NPointDomain d (m + 1), (0 : ℂ))) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      bound hF_meas hbound hbound_integrable (by simpa [F, l] using hpointwise)
  have heq :
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              φ x)
        =ᶠ[l]
      (fun ε : ℝ => ∫ x : NPointDomain d (m + 1), F ε x) := by
    filter_upwards [hperm_integrable, hcan_integrable] with ε hp hc
    rw [← MeasureTheory.integral_sub hp hc]
    congr 1
    ext x
    simp [F]
    ring
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa using hDCT

/-- Integral reduced two-direction boundary convergence from pointwise
convergence on the support of the test function and a dominated-convergence
packet.

This is the form expected from the local Jost/Ruelle boundary theorem: the
analytic step proves pointwise convergence only at real support points, while
the test function kills the complement. -/
theorem bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : NPointDomain d (m + 1) → ℂ)
    (hpointwise :
      ∀ x, φ x ≠ 0 →
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0))
    (bound : NPointDomain d (m + 1) → ℝ)
    (hF_meas :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        AEStronglyMeasurable
          (fun x : NPointDomain d (m + 1) =>
            (bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
          ‖(bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x‖ ≤ bound x)
    (hperm_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) volume)
    (hcan_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
              φ x) volume) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              φ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_pointwise_bound
      (d := d) OS lgc m i j φ bound ?_
      hF_meas hbound_integrable hbound hperm_integrable hcan_integrable
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxφ : φ x = 0
  · simp [hxφ]
  · simpa using (hpointwise x hxφ).mul tendsto_const_nhds

/-- Reduced two-direction DCT with the routine measurability and branch
integrability hypotheses discharged from the selected forward-tube witness.

The remaining inputs are exactly the genuine analytic payload: pointwise
Ruelle/Jost boundary convergence on the support of the test function and one
integrable collar bound for the branch difference. -/
theorem bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise_bound'
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d (m + 1))
    (hpointwise :
      ∀ x, φ x ≠ 0 →
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0))
    (bound : NPointDomain d (m + 1) → ℝ)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
          ‖(bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I)) *
              φ x‖ ≤ bound x) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              φ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  exact
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise_bound
      (d := d) OS lgc m i j
      (φ : NPointDomain d (m + 1) → ℂ)
      hpointwise bound
      (bvt_F_reduced_two_direction_difference_aestronglyMeasurable_eventually
        (d := d) OS lgc m i j φ)
      hbound_integrable hbound
      (bvt_F_reduced_permuted_integrable_eventually
        (d := d) OS lgc m i j φ)
      (bvt_F_reduced_canonical_integrable_eventually
        (d := d) OS lgc m φ)

/-- Reduced two-direction integral convergence from the genuine support-wise
pointwise Ruelle/Jost boundary equality alone.

The uniform domination, measurability, and branch integrability are supplied by
the selected witness' global forward-tube growth. -/
theorem bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d (m + 1))
    (hpointwise :
      ∀ x, φ x ≠ 0 →
        Filter.Tendsto
          (fun ε : ℝ =>
            bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I))
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              φ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  obtain ⟨bound, hbound_integrable, hbound⟩ :=
    bvt_F_reduced_two_direction_difference_bound_eventually
      (d := d) OS lgc m i j φ
  exact
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise_bound'
      (d := d) OS lgc m i j φ hpointwise
      bound hbound_integrable hbound

/-- Integral reduced two-direction boundary convergence from a reduced PET
extension, PET support data, and a dominated convergence packet.

The hypotheses are intentionally explicit: the remaining hard work is to supply
the real reduced PET support and compact-support domination from the reduced
Jost/Ruelle geometry, not to hide them behind another locality assumption. -/
theorem bvt_F_reduced_two_direction_integral_tendsto_zero_of_reducedExtension_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (Fred : BHW.ReducedBHWExtensionData (d := d) (n := m + 1)
      (bvt_F_reduced (d := d) OS lgc m))
    (φ : NPointDomain d (m + 1) → ℂ)
    (hreal_pet :
      ∀ x, φ x ≠ 0 →
        (fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ)) ∈
          BHW.ReducedPermutedExtendedTubeN d m)
    (bound : NPointDomain d (m + 1) → ℝ)
    (hF_meas :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        AEStronglyMeasurable
          (fun x : NPointDomain d (m + 1) =>
            (bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)) *
              φ x) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        ∀ᵐ x : NPointDomain d (m + 1) ∂volume,
          ‖(bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) -
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)) *
              φ x‖ ≤ bound x)
    (hperm_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) volume)
    (hcan_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
              φ x) volume) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              φ x) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
              φ x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  refine
    bvt_F_reduced_two_direction_integral_tendsto_zero_of_support_pointwise_bound
      (d := d) OS lgc m i j φ ?_ bound
      hF_meas hbound_integrable hbound hperm_integrable hcan_integrable
  intro x hxφ
  exact
    bvt_F_reduced_two_direction_pointwise_tendsto_zero_of_reducedExtension
      (d := d) OS lgc m i j Fred
      (BHW.reducedDiffMapReal (m + 1) d x)
      (hreal_pet x hxφ)

omit [NeZero d] in
/-- Absolute real PET membership descends to reduced PET membership after
passing to successive real differences. -/
theorem reducedDiffMapReal_mem_reducedPermutedExtendedTubeN_of_realEmbed_mem_permutedExtendedTube
    (m : ℕ) (x : NPointDomain d (m + 1))
    (hxPET : BHW.realEmbed x ∈ BHW.PermutedExtendedTube d (m + 1)) :
    (fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d m := by
  refine ⟨BHW.realEmbed x, hxPET, ?_⟩
  ext k μ
  rw [BHW.reducedDiffMap_eq_successive_differences,
    BHW.reducedDiffMapReal_apply]
  simp [BHW.realEmbed]

omit [NeZero d] in
/-- A real forward-Jost configuration gives reduced PET membership for its
successive real differences. -/
theorem reducedDiffMapReal_mem_reducedPermutedExtendedTubeN_of_forwardJostSet
    (m : ℕ) (hd : 1 ≤ d) (x : NPointDomain d (m + 1))
    (hxFJ : x ∈ BHW.ForwardJostSet d (m + 1) hd) :
    (fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ)) ∈
      BHW.ReducedPermutedExtendedTubeN d m := by
  exact
    reducedDiffMapReal_mem_reducedPermutedExtendedTubeN_of_realEmbed_mem_permutedExtendedTube
      (d := d) m x
      (BHW.extendedTube_subset_permutedExtendedTube
        (BHW.forwardJostSet_subset_extendedTube
          (d := d) (n := m + 1) hd x hxFJ))

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

omit [NeZero d] in
private theorem npoint_integral_perm_eq_self {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun k => x (σ k)) =
    ∫ x : NPointDomain d n, h x :=
  (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp' h

/-- Pair-specific algebraic reduction of the compact canonical-shell swap
difference to a reduced two-direction boundary difference.

This is the adjacent-ready form of
`compact_canonicalShell_swap_tendsto_of_reduced_two_direction_tendsto`: the
reduced limit is required only for the concrete pair being transported. -/
theorem compact_canonicalShell_swap_tendsto_of_reduced_pair_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (f g : SchwartzNPoint d (m + 1))
    (hf_compact : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ))
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j))
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k)))
    (hreduced_limit :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d (m + 1),
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε *
                      permutedCanonicalReducedDirectionC
                        (d := d) m (Equiv.swap i j) k μ *
                      Complex.I) *
                (f x)) -
            ∫ x : NPointDomain d (m + 1),
              bvt_F_reduced (d := d) OS lgc m
                (fun k μ =>
                  (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                    ε * canonicalReducedDirectionC (d := d) m k μ *
                      Complex.I) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F OS lgc (m + 1)
              (canonicalShell (d := d) (m + 1) x ε) *
              (g x)) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F OS lgc (m + 1)
              (canonicalShell (d := d) (m + 1) x ε) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have _ : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) := hf_compact
  have _ : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) := hsp
  let n : ℕ := m + 1
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hswap_arg :
      ∀ x : NPointDomain d n,
        g (fun k => x (σ k)) = f x := by
    intro x
    have hx := hswap (fun k => x (σ k))
    have harg :
        (fun k => (fun l => x (σ l)) (Equiv.swap i j k)) = x := by
      funext k
      simp [n, σ]
    simpa [n, σ, harg] using hx
  have hpermuted_shell :
      ∀ (x : NPointDomain d n) (ε : ℝ),
        bvt_F OS lgc n
            (canonicalShell (d := d) n (fun k => x (σ k)) ε) =
          bvt_F OS lgc n
            (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) := by
    intro x ε
    have hperm :=
      bvt_F_perm (d := d) OS lgc n σ
        (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε)
    have hcfg :
        (fun k =>
          permutedEtaCanonicalShellOfPerm (d := d) n σ x ε (σ k)) =
        canonicalShell (d := d) n (fun k => x (σ k)) ε := by
      funext k μ
      simp [canonicalShell, permutedEtaCanonicalShellOfPerm, σ]
    rw [← hcfg]
    exact hperm
  have hchange :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) =
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x) := by
    intro ε
    let h : NPointDomain d n → ℂ :=
      fun x => bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)
    calc
      (∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x))
          = ∫ x : NPointDomain d n, h x := by rfl
      _ = ∫ x : NPointDomain d n, h (fun k => x (σ k)) := by
            exact (npoint_integral_perm_eq_self (d := d) σ h).symm
      _ = ∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by
              simp only [h]
              rw [hpermuted_shell x ε, hswap_arg x]
  have hreduce_perm :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x)) =
          ∫ x : NPointDomain d n,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              (f x) := by
    intro ε
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      have hfac :=
        bvt_F_eq_bvt_F_reduced_reducedDiffMap
          (d := d) OS lgc m
          (permutedEtaCanonicalShellOfPerm (d := d) (m + 1)
            (Equiv.swap i j) x ε)
      have hred :=
        reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
          (d := d) m (Equiv.swap i j) x ε
      calc
        bvt_F OS lgc n
            (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) * f x
            =
          bvt_F_reduced (d := d) OS lgc m
            (BHW.reducedDiffMap (m + 1) d
              (permutedEtaCanonicalShellOfPerm (d := d) (m + 1)
                (Equiv.swap i j) x ε)) * f x := by
              simpa [n, σ] using congrArg (fun z => z * f x) hfac
        _ =
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) * f x := by
              rw [hred]
  have hreduce_canon :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) *
              (f x)) =
          ∫ x : NPointDomain d n,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x) := by
    intro ε
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      have hfac :=
        bvt_F_eq_bvt_F_reduced_reducedDiffMap
          (d := d) OS lgc m
          (canonicalShell (d := d) (m + 1) x ε)
      have hred :=
        reducedDiffMap_canonicalShell_eq (d := d) m x ε
      calc
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * f x
            =
          bvt_F_reduced (d := d) OS lgc m
            (BHW.reducedDiffMap (m + 1) d
              (canonicalShell (d := d) (m + 1) x ε)) * f x := by
              simpa [n] using congrArg (fun z => z * f x) hfac
        _ =
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
            f x := by
              rw [hred]
  refine hreduced_limit.congr' ?_
  exact Filter.Eventually.of_forall fun ε => by
    change
      ((∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            (f x)) -
        ∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            (f x)) =
      ((∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) -
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x))
    calc
      ((∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            (f x)) -
        ∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            (f x))
          =
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x)) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
            rw [hreduce_perm ε, hreduce_canon ε]
      _ =
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
            rw [hchange ε]

/-- Adjacent-only reduced Ruelle/Jost producer for theorem 2.

This is the honest remaining analytic theorem after the algebraic reduced
transport and compact-density layers: for compact tests supported on the
adjacent reduced spacelike edge, the canonical and adjacent-swapped reduced
positive-height approaches have the same distributional boundary limit. -/
def AdjacentReducedRuelleDistributionalLimit
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f : SchwartzNPoint d (m + 1)),
    HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
    (∀ x, f.toFun x ≠ 0 →
      BHW.reducedDiffMapReal (m + 1) d x ∈
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) →
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) *
              (f x)) -
          ∫ x : NPointDomain d (m + 1),
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

/-- The adjacent reduced Ruelle/Jost producer closes the live theorem-2
adjacent locality statement. -/
theorem bvt_W_swap_pairing_of_spacelike_from_adjacent_reduced_ruelle_distributional
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hRuelle : AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  intro n i hi f g hsp hswap
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      exact
        bv_local_commutativity_transfer_of_adjacent_swap_pairing_tendsto
          (d := d) (m + 1) (bvt_W OS lgc (m + 1)) (bvt_F OS lgc (m + 1))
          (bvt_W_continuous (d := d) OS lgc (m + 1))
          (bvt_boundary_values (d := d) OS lgc (m + 1))
          i hi
          (by
            intro f g hf_compact hsp hswap
            let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
            have hred_support :
                ∀ x, f.toFun x ≠ 0 →
                  BHW.reducedDiffMapReal (m + 1) d x ∈
                    reducedSpacelikeSwapEdge (d := d) m i j := by
              intro x hx
              exact
                reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
                  (d := d) m i j x (hsp x hx)
            exact
              compact_canonicalShell_swap_tendsto_of_reduced_pair_tendsto
                (d := d) OS lgc m i j f g hf_compact hsp hswap
                (hRuelle m i hi f hf_compact hred_support))
          f g hsp hswap

/-- Algebraic reduction of the compact canonical-shell swap difference to the
reduced two-direction boundary difference.

This theorem is the production version of the scratch reduction in
`test/proofideas_theorem2_reduced_boundary_algebra.lean`.  It performs only
the swap change of variables, `bvt_F` permutation invariance, and the
translation-invariant factorization through reduced differences.  The genuine
analytic input remains the reduced two-direction boundary-deformation limit in
the hypothesis. -/
theorem compact_canonicalShell_swap_tendsto_of_reduced_two_direction_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hreduced_limit :
      ∀ (m : ℕ) (i j : Fin (m + 1)) (f : SchwartzNPoint d (m + 1)),
        HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
        (∀ x, f.toFun x ≠ 0 →
          BHW.reducedDiffMapReal (m + 1) d x ∈
            reducedSpacelikeSwapEdge (d := d) m i j) →
        Filter.Tendsto
          (fun ε : ℝ =>
            (∫ x : NPointDomain d (m + 1),
                bvt_F_reduced (d := d) OS lgc m
                  (fun k μ =>
                    (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                      ε *
                        permutedCanonicalReducedDirectionC
                          (d := d) m (Equiv.swap i j) k μ *
                        Complex.I) *
                  (f x)) -
              ∫ x : NPointDomain d (m + 1),
                bvt_F_reduced (d := d) OS lgc m
                  (fun k μ =>
                    (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                      ε * canonicalReducedDirectionC (d := d) m k μ *
                        Complex.I) *
                  (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0)) :
    ∀ (m : ℕ) (i j : Fin (m + 1)) (f g : SchwartzNPoint d (m + 1)),
      HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (g x)) -
            ∫ x : NPointDomain d (m + 1),
              bvt_F OS lgc (m + 1)
                (canonicalShell (d := d) (m + 1) x ε) *
                (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro m i j f g hf_compact hsp hswap
  let n : ℕ := m + 1
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hσσ : ∀ k : Fin n, σ (σ k) = k := by
    intro k
    simp [σ]
  have hswap_arg :
      ∀ x : NPointDomain d n,
        g (fun k => x (σ k)) = f x := by
    intro x
    have hx := hswap (fun k => x (σ k))
    have harg :
        (fun k => (fun l => x (σ l)) (Equiv.swap i j k)) = x := by
      funext k
      simp [n, σ]
    simpa [n, σ, harg] using hx
  have hpermuted_shell :
      ∀ (x : NPointDomain d n) (ε : ℝ),
        bvt_F OS lgc n
            (canonicalShell (d := d) n (fun k => x (σ k)) ε) =
          bvt_F OS lgc n
            (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) := by
    intro x ε
    have hperm :=
      bvt_F_perm (d := d) OS lgc n σ
        (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε)
    have hcfg :
        (fun k =>
          permutedEtaCanonicalShellOfPerm (d := d) n σ x ε (σ k)) =
        canonicalShell (d := d) n (fun k => x (σ k)) ε := by
      funext k μ
      simp [canonicalShell, permutedEtaCanonicalShellOfPerm, σ]
    rw [← hcfg]
    exact hperm
  have hchange :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) =
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x) := by
    intro ε
    let h : NPointDomain d n → ℂ :=
      fun x => bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)
    calc
      (∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x))
          = ∫ x : NPointDomain d n, h x := by rfl
      _ = ∫ x : NPointDomain d n, h (fun k => x (σ k)) := by
            exact (npoint_integral_perm_eq_self (d := d) σ h).symm
      _ = ∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by
              simp only [h]
              rw [hpermuted_shell x ε, hswap_arg x]
  have hreduce_perm :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x)) =
          ∫ x : NPointDomain d n,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              (f x) := by
    intro ε
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      have hfac :=
        bvt_F_eq_bvt_F_reduced_reducedDiffMap
          (d := d) OS lgc m
          (permutedEtaCanonicalShellOfPerm (d := d) (m + 1)
            (Equiv.swap i j) x ε)
      have hred :=
        reducedDiffMap_permutedEtaCanonicalShellOfPerm_eq
          (d := d) m (Equiv.swap i j) x ε
      calc
        bvt_F OS lgc n
            (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) * f x
            =
          bvt_F_reduced (d := d) OS lgc m
            (BHW.reducedDiffMap (m + 1) d
              (permutedEtaCanonicalShellOfPerm (d := d) (m + 1)
                (Equiv.swap i j) x ε)) * f x := by
              simpa [n, σ] using congrArg (fun z => z * f x) hfac
        _ =
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) * f x := by
              rw [hred]
  have hreduce_canon :
      ∀ ε : ℝ,
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) *
              (f x)) =
          ∫ x : NPointDomain d n,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              (f x) := by
    intro ε
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      have hfac :=
        bvt_F_eq_bvt_F_reduced_reducedDiffMap
          (d := d) OS lgc m
          (canonicalShell (d := d) (m + 1) x ε)
      have hred :=
        reducedDiffMap_canonicalShell_eq (d := d) m x ε
      calc
        bvt_F OS lgc n (canonicalShell (d := d) n x ε) * f x
            =
          bvt_F_reduced (d := d) OS lgc m
            (BHW.reducedDiffMap (m + 1) d
              (canonicalShell (d := d) (m + 1) x ε)) * f x := by
              simpa [n] using congrArg (fun z => z * f x) hfac
        _ =
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) *
            f x := by
              rw [hred]
  have hred_support :
      ∀ x, f.toFun x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
    intro x hx
    exact
      reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
        (d := d) m i j x (hsp x hx)
  have hlim := hreduced_limit m i j f hf_compact hred_support
  refine hlim.congr' ?_
  exact Filter.Eventually.of_forall fun ε => by
    change
      ((∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            (f x)) -
        ∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            (f x)) =
      ((∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) -
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x))
    calc
      ((∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε *
                  permutedCanonicalReducedDirectionC
                    (d := d) m (Equiv.swap i j) k μ *
                  Complex.I) *
            (f x)) -
        ∫ x : NPointDomain d n,
          bvt_F_reduced (d := d) OS lgc m
            (fun k μ =>
              (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) +
                ε * canonicalReducedDirectionC (d := d) m k μ *
                  Complex.I) *
            (f x))
          =
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n
              (permutedEtaCanonicalShellOfPerm (d := d) n σ x ε) *
              (f x)) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
            rw [hreduce_perm ε, hreduce_canon ε]
      _ =
        (∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (g x)) -
          ∫ x : NPointDomain d n,
            bvt_F OS lgc n (canonicalShell (d := d) n x ε) * (f x) := by
            rw [hchange ε]
