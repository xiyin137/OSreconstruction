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

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The canonical reduced imaginary direction: every reduced difference slot
uses the fixed future-timelike safe basepoint vector. -/
def canonicalReducedDirection (m : ℕ) : Fin m → Fin (d + 1) → ℝ :=
  fun _ μ => BHW.safeBasepointVec d μ

/-- Complex-valued version of `canonicalReducedDirection`. -/
def canonicalReducedDirectionC (m : ℕ) : BHW.ReducedNPointConfig d m :=
  fun k μ => (canonicalReducedDirection (d := d) m k μ : ℂ)

/-- Canonical reduced direction after applying an absolute permutation through
the induced reduced-difference action. -/
noncomputable def permutedCanonicalReducedDirectionC
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    BHW.ReducedNPointConfig d m :=
  BHW.permOnReducedDiff (d := d) (n := m + 1) σ
    (canonicalReducedDirectionC (d := d) m)

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

private theorem continuous_reducedPairDiff
    (m : ℕ) (i j : Fin (m + 1)) :
    Continuous (reducedPairDiff (d := d) m i j) := by
  have hpre := continuous_prependBasepointReal_zero (d := d) m
  have hrec : Continuous (fun ξ : NPointDomain d m =>
      (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m 0 ξ)) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm.continuous.comp hpre
  apply continuous_pi
  intro μ
  exact
    ((continuous_apply μ).comp ((continuous_apply j).comp hrec)).sub
      ((continuous_apply μ).comp ((continuous_apply i).comp hrec))

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
