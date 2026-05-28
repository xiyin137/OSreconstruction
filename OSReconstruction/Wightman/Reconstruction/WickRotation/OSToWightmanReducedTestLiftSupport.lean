import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced

/-!
# Reduced test-lift support bridges

Small neutral support facts for the reduced theorem-2 route.  These lemmas keep
the basepoint quotient and adjacent reduced-coordinate support transport out of
the large frontier files.
-/

open scoped Classical NNReal
open BigOperators MeasureTheory

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

theorem minkowski_isSpacelike_neg_iff
    (v : MinkowskiSpace d) :
    MinkowskiSpace.IsSpacelike d (-v) ↔
      MinkowskiSpace.IsSpacelike d v := by
  unfold MinkowskiSpace.IsSpacelike MinkowskiSpace.minkowskiNormSq
  rw [MinkowskiSpace.minkowskiInner_neg_left,
    MinkowskiSpace.minkowskiInner_neg_right]
  ring_nf

/-- Reduced support on the selected adjacent reduced edge lifts to public
adjacent spacelike support after inserting a basepoint cutoff. -/
theorem reducedTestLift_support_adjacent_spacelike
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      ∀ ξ, φ.toFun ξ ≠ 0 →
        ξ ∈ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    ∀ x, (BHW.reducedTestLift m d χ φ).toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩) := by
  intro x hx
  have hφ_ne :
      φ.toFun (BHW.reducedDiffMapReal (m + 1) d x) ≠ 0 := by
    intro hzero
    apply hx
    change (BHW.reducedTestLift m d χ φ) x = 0
    rw [BHW.reducedTestLift_apply]
    rw [mul_eq_zero]
    exact Or.inr hzero
  have hedge :=
    hφ_support (BHW.reducedDiffMapReal (m + 1) d x) hφ_ne
  have hselected :
      MinkowskiSpace.IsSpacelike d
        (BHW.reducedDiffMapReal (m + 1) d x ⟨i.val, by omega⟩) := by
    simpa [mem_reducedSpacelikeSwapEdge_adjacent_iff] using hedge
  have hcoord :
      BHW.reducedDiffMapReal (m + 1) d x ⟨i.val, by omega⟩ =
        fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ := by
    ext μ
    simpa using
      BHW.reducedDiffMapReal_apply (m + 1) d x ⟨i.val, by omega⟩ μ
  have hneg :
      MinkowskiSpace.IsSpacelike d
        (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) := by
    have hraw :
        MinkowskiSpace.IsSpacelike d
          (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) := by
      simpa [hcoord] using hselected
    have hfun :
        (fun μ => x i μ - x ⟨i.val + 1, hi⟩ μ) =
          -(fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ) := by
      funext μ
      simp
    rw [hfun]
    exact (minkowski_isSpacelike_neg_iff (d := d)
      (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ)).2 hraw
  simpa [MinkowskiSpace.AreSpacelikeSeparated, Pi.sub_apply] using hneg

/-- The basepoint cutoff in `reducedTestLift` integrates out against any
reduced-coordinate integrand, provided the lifted absolute integrand is
integrable. -/
theorem integral_reducedTestLift_eq_reduced
    (m : ℕ) (χ : BHW.NormalizedBasepointCutoff d)
    (φ : SchwartzNPoint d m) (G : NPointDomain d m → ℂ)
    (hG :
      Integrable
        (fun x : NPointDomain d (m + 1) =>
          G (BHW.reducedDiffMapReal (m + 1) d x) *
            BHW.reducedTestLift m d χ.toSchwartz φ x) volume) :
    (∫ x : NPointDomain d (m + 1),
        G (BHW.reducedDiffMapReal (m + 1) d x) *
          BHW.reducedTestLift m d χ.toSchwartz φ x)
      =
    ∫ ξ : NPointDomain d m, G ξ * φ ξ := by
  let H : NPointDomain d (m + 1) → ℂ := fun x =>
    G (BHW.reducedDiffMapReal (m + 1) d x) *
      BHW.reducedTestLift m d χ.toSchwartz φ x
  rw [BHW.integral_realDiffCoord_change_variables (d := d) m H hG]
  have hred :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        BHW.reducedDiffMapReal (m + 1) d
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) = ξ := by
    intro ξ x₀
    exact BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
      (d := d) (m := m) x₀ ξ
  have hlift :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        BHW.reducedTestLift m d χ.toSchwartz φ
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) =
          χ.toSchwartz x₀ * φ ξ := by
    intro ξ x₀
    exact BHW.reducedTestLift_apply_realDiffCoordCLE_symm_prependBasepointReal
      (m := m) (d := d) (χ := χ.toSchwartz) (φ := φ) x₀ ξ
  simp_rw [H, hred, hlift]
  simp_rw [show ∀ (a b c : ℂ), a * (b * c) = (a * c) * b by
    intro a b c
    ring]
  simp_rw [← smul_eq_mul (a := _ * _), MeasureTheory.integral_smul, smul_eq_mul]
  simp [χ.integral_eq_one]

/-- Basepoint fiber marginal of an absolute test in real difference
coordinates. -/
noncomputable def reducedFiberIntegral
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ) :
    NPointDomain d m → ℂ :=
  fun ξ => ∫ x₀ : SpacetimeDim d,
    f ((BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m x₀ ξ))

/-- If the branch factor depends only on reduced differences, the absolute
integral is the reduced integral against the basepoint fiber marginal. -/
theorem integral_reducedFiberIntegral_eq
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ)
    (G : NPointDomain d m → ℂ)
    (hGf : Integrable
      (fun x : NPointDomain d (m + 1) =>
        G (BHW.reducedDiffMapReal (m + 1) d x) * f x) volume) :
    (∫ x : NPointDomain d (m + 1),
        G (BHW.reducedDiffMapReal (m + 1) d x) * f x) =
      ∫ ξ : NPointDomain d m, G ξ * reducedFiberIntegral (d := d) m f ξ := by
  let H : NPointDomain d (m + 1) → ℂ := fun x =>
    G (BHW.reducedDiffMapReal (m + 1) d x) * f x
  rw [BHW.integral_realDiffCoord_change_variables (d := d) m H hGf]
  have hred :
      ∀ (ξ : NPointDomain d m) (x₀ : SpacetimeDim d),
        BHW.reducedDiffMapReal (m + 1) d
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) = ξ := by
    intro ξ x₀
    exact BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
      (d := d) (m := m) x₀ ξ
  simp_rw [H, hred]
  congr 1
  funext ξ
  change (∫ x₀ : SpacetimeDim d,
      (G ξ) • f ((BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ))) =
    G ξ * reducedFiberIntegral (d := d) m f ξ
  rw [MeasureTheory.integral_smul]
  simp [reducedFiberIntegral, smul_eq_mul]

omit [NeZero d] in
/-- The fiber marginal can be nonzero only over reduced coordinates that occur
above a nonzero absolute test value. -/
theorem reducedFiberIntegral_support_subset_of_absolute_reduced_support
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ)
    (S : Set (NPointDomain d m))
    (hf_support :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈ S) :
    Function.support (reducedFiberIntegral (d := d) m f) ⊆ S := by
  intro ξ hξ
  by_contra hξS
  have hzero :
      ∀ x₀ : SpacetimeDim d,
        f ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) = 0 := by
    intro x₀
    by_contra hx₀
    have hred :
        BHW.reducedDiffMapReal (m + 1) d
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) = ξ :=
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) (m := m) x₀ ξ
    have hS_abs :=
      hf_support
        ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) hx₀
    have hS_ξ : ξ ∈ S := by
      rw [hred] at hS_abs
      exact hS_abs
    exact hξS hS_ξ
  have hmargin_zero : reducedFiberIntegral (d := d) m f ξ = 0 := by
    simp [reducedFiberIntegral, hzero]
  exact hξ hmargin_zero

omit [NeZero d] in
/-- Compact absolute support projects to compact support of the basepoint fiber
marginal. -/
theorem reducedFiberIntegral_hasCompactSupport
    (m : ℕ) (f : NPointDomain d (m + 1) → ℂ)
    (hf_compact : HasCompactSupport f) :
    HasCompactSupport (reducedFiberIntegral (d := d) m f) := by
  let K : Set (NPointDomain d m) :=
    BHW.reducedDiffMapRealCLM (m + 1) d ''
      tsupport (f : NPointDomain d (m + 1) → ℂ)
  have hK_compact : IsCompact K := by
    exact hf_compact.isCompact.image
      (BHW.reducedDiffMapRealCLM (m + 1) d).continuous
  have hf_support_to_K :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈ K := by
    intro x hx
    exact ⟨x, subset_tsupport _ hx, rfl⟩
  have hsupport :
      Function.support (reducedFiberIntegral (d := d) m f) ⊆ K :=
    reducedFiberIntegral_support_subset_of_absolute_reduced_support
      (d := d) m f K hf_support_to_K
  exact HasCompactSupport.of_support_subset_isCompact hK_compact hsupport

/-- Fiber marginal of an absolute Schwartz test, named for the canonical-swap
normal form of the reduced Ruelle theorem. -/
def reducedFiberMarginal
    (m : ℕ) (f : SchwartzNPoint d (m + 1)) :
    NPointDomain d m → ℂ :=
  reducedFiberIntegral (d := d) m
    (f : NPointDomain d (m + 1) → ℂ)

/-- The basepoint fiber marginal of a normalized reduced test lift is exactly
the original reduced test.  This is the concrete bridge between the book's
reduced test-function formulation and the current fiber-marginal formulation. -/
theorem reducedFiberMarginal_reducedTestLift_eq
    (m : ℕ) (χ : BHW.NormalizedBasepointCutoff d)
    (φ : SchwartzNPoint d m) :
    reducedFiberMarginal (d := d) m
      (BHW.reducedTestLift m d χ.toSchwartz φ) =
        (φ : NPointDomain d m → ℂ) := by
  funext ξ
  change
    reducedFiberIntegral (d := d) m
      (BHW.reducedTestLift m d χ.toSchwartz φ :
        NPointDomain d (m + 1) → ℂ) ξ = φ ξ
  simp only [reducedFiberIntegral]
  have hlift :
      ∀ x₀ : SpacetimeDim d,
        BHW.reducedTestLift m d χ.toSchwartz φ
          ((BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ)) =
          χ.toSchwartz x₀ * φ ξ := by
    intro x₀
    exact
      BHW.reducedTestLift_apply_realDiffCoordCLE_symm_prependBasepointReal
        (m := m) (d := d) (χ := χ.toSchwartz) (φ := φ) x₀ ξ
  simp_rw [hlift]
  have hfun :
      (fun x₀ : SpacetimeDim d => χ.toSchwartz x₀ * φ ξ) =
        fun x₀ : SpacetimeDim d => (φ ξ) • χ.toSchwartz x₀ := by
    ext x₀
    simp [smul_eq_mul, mul_comm]
  rw [hfun, MeasureTheory.integral_smul]
  simp [χ.integral_eq_one]

/-- Adjacent-swapped reduced positive approach. -/
def adjacentReducedPermutedBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ℝ → NPointDomain d m → ℂ :=
  fun ε ξ =>
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε *
            permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
            Complex.I)

/-- Canonical reduced positive approach based at the real reduced point after
the induced adjacent transposition. -/
def canonicalAfterReducedSwapBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) :
    ℝ → NPointDomain d m → ℂ :=
  fun ε ξ =>
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
            (fun k μ => (ξ k μ : ℂ)) k μ +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)

/-- Canonical reduced positive approach at the original real reduced point. -/
def canonicalReducedBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) :
    ℝ → NPointDomain d m → ℂ :=
  fun ε ξ =>
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)

/-- Difference of two reduced branch pairings against a fixed fiber marginal. -/
def reducedFiberBranchDifference
    (m : ℕ)
    (G H : ℝ → NPointDomain d m → ℂ)
    (Φ : NPointDomain d m → ℂ) :
    ℝ → ℂ :=
  fun ε =>
    (∫ ξ : NPointDomain d m, G ε ξ * Φ ξ) -
      ∫ ξ : NPointDomain d m, H ε ξ * Φ ξ

/-- Fiber-marginal difference using the adjacent-swapped reduced approach. -/
def adjacentReducedFiberDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (f : SchwartzNPoint d (m + 1)) :
    ℝ → ℂ :=
  reducedFiberBranchDifference (d := d) m
    (adjacentReducedPermutedBranch (d := d) OS lgc m i j)
    (canonicalReducedBranch (d := d) OS lgc m)
    (reducedFiberMarginal (d := d) m f)

/-- Fiber-marginal difference in canonical-after-reduced-swap normal form. -/
def canonicalSwapReducedFiberDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (f : SchwartzNPoint d (m + 1)) :
    ℝ → ℂ :=
  reducedFiberBranchDifference (d := d) m
    (canonicalAfterReducedSwapBranch (d := d) OS lgc m i j)
    (canonicalReducedBranch (d := d) OS lgc m)
    (reducedFiberMarginal (d := d) m f)

/-- The adjacent-swapped reduced positive approach is exactly the canonical
positive approach after applying the induced reduced adjacent transposition to
the real reduced base point. -/
theorem adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ε : ℝ) (ξ : NPointDomain d m) :
    adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ =
      canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ := by
  simp only [adjacentReducedPermutedBranch,
    canonicalAfterReducedSwapBranch]
  calc
    bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          (ξ k μ : ℂ) +
            ε * permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
              Complex.I)
        =
      bvt_F_reduced (d := d) OS lgc m
        (BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
          (fun k μ =>
            (ξ k μ : ℂ) +
              ε *
                permutedCanonicalReducedDirectionC (d := d) m (Equiv.swap i j) k μ *
                Complex.I)) := by
          exact bvt_F_reduced_permutedDirection_to_realPermutedCanonical
            (d := d) OS lgc m i j ξ ε
    _ =
      bvt_F_reduced (d := d) OS lgc m
        (fun k μ =>
          BHW.permOnReducedDiff (d := d) (n := m + 1) (Equiv.swap i j)
              (fun k μ => (ξ k μ : ℂ)) k μ +
            ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
          congr 1
          exact
            permOnReducedDiff_permutedReducedApproach_eq_canonical
              (d := d) m i j ξ ε

/-- Integral normal form of the fiber-marginal adjacent reduced Ruelle
difference.  The remaining analytic theorem can be proved in the canonical
boundary-distribution form after the reduced swap. -/
theorem adjacentReducedFiberDifference_eq_canonicalSwapReducedFiberDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (f : SchwartzNPoint d (m + 1)) :
    adjacentReducedFiberDifference (d := d) OS lgc m i j f =
      canonicalSwapReducedFiberDifference (d := d) OS lgc m i j f := by
  funext ε
  simp only [adjacentReducedFiberDifference,
    canonicalSwapReducedFiberDifference, reducedFiberBranchDifference]
  congr 1
  · refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun ξ => by
      change
        adjacentReducedPermutedBranch (d := d) OS lgc m i j ε ξ *
            reducedFiberMarginal (d := d) m f ξ =
          canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ *
            reducedFiberMarginal (d := d) m f ξ
      rw [adjacentReducedPermutedBranch_eq_canonicalAfterReducedSwapBranch
        (d := d) OS lgc m i j ε ξ]

omit [NeZero d] in
/-- Real form of the induced reduced permutation action. -/
def realPermOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) : NPointDomain d m :=
  fun k μ =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
      (fun k μ => (ξ k μ : ℂ)) k μ).re

omit [NeZero d] in
/-- Complexifying the real induced reduced permutation recovers the complex
induced action on real reduced configurations. -/
theorem ofReal_realPermOnReducedDiff_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) :
    (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ
        (fun k μ => (ξ k μ : ℂ)) := by
  ext k μ
  apply Complex.ext
  · simp [realPermOnReducedDiff]
  · exact (permOnReducedDiff_ofReal_im_zero (d := d) m σ ξ k μ).symm

omit [NeZero d] in
/-- Quotienting absolute coordinates to reduced differences commutes with
absolute permutation, when the absolute configuration is written in basepoint
plus reduced-difference coordinates. -/
theorem reducedDiffMapReal_permute_realDiffCoordCLE_symm_prependBasepointReal
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x₀ : SpacetimeDim d) (ξ : NPointDomain d m) :
    BHW.reducedDiffMapReal (m + 1) d
        (fun k =>
          (BHW.realDiffCoordCLE (m + 1) d).symm
            (BHW.prependBasepointReal d m x₀ ξ) (σ k)) =
      realPermOnReducedDiff (d := d) m σ ξ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let y : NPointDomain d (m + 1) :=
    (BHW.realDiffCoordCLE (m + 1) d).symm
      (BHW.prependBasepointReal d m x₀ ξ)
  let z : Fin (m + 1) → Fin (d + 1) → ℂ :=
    fun k μ => (y k μ : ℂ)
  have hred_real :
      BHW.reducedDiffMapReal (m + 1) d y = ξ := by
    simpa [y] using
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        (d := d) (m := m) x₀ ξ
  have hred_complex :
      BHW.reducedDiffMap (m + 1) d z =
        fun k μ => (ξ k μ : ℂ) := by
    ext k μ
    have h :
        y ⟨k.val + 1, by omega⟩ μ -
            y ⟨k.val, by omega⟩ μ =
          ξ k μ := by
      simpa [BHW.reducedDiffMapReal_apply] using
        congrFun (congrFun hred_real k) μ
    rw [BHW.reducedDiffMap_eq_successive_differences]
    change ((y ⟨k.val + 1, by omega⟩ μ : ℂ) -
        (y ⟨k.val, by omega⟩ μ : ℂ)) = (ξ k μ : ℂ)
    simpa using congrArg (fun r : ℝ => (r : ℂ)) h
  have hperm_complex :
      (fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d
          (fun k => y (σ k)) k μ : ℂ)) =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ) := by
    calc
      (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d
            (fun k => y (σ k)) k μ : ℂ))
          =
        BHW.reducedDiffMap (m + 1) d (fun k μ => z (σ k) μ) := by
          ext k μ
          rw [BHW.reducedDiffMap_eq_successive_differences]
          change
            ((y (σ ⟨k.val + 1, by omega⟩) μ -
                y (σ ⟨k.val, by omega⟩) μ : ℝ) : ℂ) =
              (y (σ ⟨k.val + 1, by omega⟩) μ : ℂ) -
                (y (σ ⟨k.val, by omega⟩) μ : ℂ)
          simp
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d z) := by
          exact (BHW.permOnReducedDiff_reducedDiffMap
            (d := d) (n := m + 1) σ z).symm
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (fun k μ => (ξ k μ : ℂ)) := by
          exact congrArg
            (fun η =>
              BHW.permOnReducedDiff (d := d) (n := m + 1) σ η)
            hred_complex
      _ =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ) := by
          simpa using
            (ofReal_realPermOnReducedDiff_eq (d := d) m σ ξ).symm
  ext k μ
  exact Complex.ofReal_injective
    (congrFun (congrFun hperm_complex k) μ)

omit [NeZero d] in
/-- Passing from absolute real configurations to reduced differences commutes
with an absolute permutation, producing the induced reduced real permutation.

This is the coordinate algebra used in the adjacent-swap locality route when
the absolute swap of neighboring fields is transported to reduced variables. -/
theorem reducedDiffMapReal_permute_absolute
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (x : NPointDomain d (m + 1)) :
    BHW.reducedDiffMapReal (m + 1) d (fun k => x (σ k)) =
      realPermOnReducedDiff (d := d) m σ
        (BHW.reducedDiffMapReal (m + 1) d x) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let z : Fin (m + 1) → Fin (d + 1) → ℂ := fun k μ => (x k μ : ℂ)
  have hred_complex :
      BHW.reducedDiffMap (m + 1) d z =
        fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ) := by
    ext k μ
    rw [BHW.reducedDiffMap_eq_successive_differences]
    rw [BHW.reducedDiffMapReal_apply]
    change ((x ⟨k.val + 1, by omega⟩ μ : ℂ) -
        (x ⟨k.val, by omega⟩ μ : ℂ)) =
      ((x ⟨k.val + 1, by omega⟩ μ -
        x ⟨k.val, by omega⟩ μ : ℝ) : ℂ)
    simp
  have hperm_complex :
      (fun k μ =>
        (BHW.reducedDiffMapReal (m + 1) d
          (fun k => x (σ k)) k μ : ℂ)) =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ
            (BHW.reducedDiffMapReal (m + 1) d x) k μ : ℂ) := by
    calc
      (fun k μ =>
          (BHW.reducedDiffMapReal (m + 1) d
            (fun k => x (σ k)) k μ : ℂ))
          =
        BHW.reducedDiffMap (m + 1) d (fun k μ => z (σ k) μ) := by
          ext k μ
          rw [BHW.reducedDiffMap_eq_successive_differences]
          rw [BHW.reducedDiffMapReal_apply]
          change
            ((x (σ ⟨k.val + 1, by omega⟩) μ -
                x (σ ⟨k.val, by omega⟩) μ : ℝ) : ℂ) =
              (x (σ ⟨k.val + 1, by omega⟩) μ : ℂ) -
                (x (σ ⟨k.val, by omega⟩) μ : ℂ)
          simp
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (BHW.reducedDiffMap (m + 1) d z) := by
          exact (BHW.permOnReducedDiff_reducedDiffMap
            (d := d) (n := m + 1) σ z).symm
      _ =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
          (fun k μ => (BHW.reducedDiffMapReal (m + 1) d x k μ : ℂ)) := by
          exact congrArg
            (fun η =>
              BHW.permOnReducedDiff (d := d) (n := m + 1) σ η)
            hred_complex
      _ =
        fun k μ =>
          (realPermOnReducedDiff (d := d) m σ
            (BHW.reducedDiffMapReal (m + 1) d x) k μ : ℂ) := by
          simpa using
            (ofReal_realPermOnReducedDiff_eq
              (d := d) m σ (BHW.reducedDiffMapReal (m + 1) d x)).symm
  ext k μ
  exact Complex.ofReal_injective
    (congrFun (congrFun hperm_complex k) μ)

omit [NeZero d] in
/-- On the selected adjacent reduced difference, the induced real adjacent
transposition acts by negation. -/
theorem realPermOnReducedDiff_adjacentSwap_selected
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ⟨i.val, by omega⟩ =
      -ξ ⟨i.val, by omega⟩ := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        ⟨i.val, by omega⟩)
      μ
  have hselectedμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_selected
        (d := d) m i hi (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ⟨i.val, by omega⟩ μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) ⟨i.val, by omega⟩ μ := hcomplexμ
    _ = -((ξ ⟨i.val, by omega⟩ μ : ℂ)) := by
        simpa using hselectedμ
    _ = ((-ξ ⟨i.val, by omega⟩ μ : ℝ) : ℂ) := by simp

omit [NeZero d] in
/-- On the predecessor reduced difference, the induced real adjacent
transposition adds the selected adjacent difference. -/
theorem realPermOnReducedDiff_adjacentSwap_prev
    (m : ℕ) (i : Fin (m + 1)) (hprev : 0 < i.val)
    (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ
        ⟨i.val - 1, by omega⟩ =
      ξ ⟨i.val - 1, by omega⟩ + ξ ⟨i.val, by omega⟩ := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        ⟨i.val - 1, by omega⟩)
      μ
  have hprevμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_prev
        (d := d) m i hprev hi (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ
        ⟨i.val - 1, by omega⟩ μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) ⟨i.val - 1, by omega⟩ μ := hcomplexμ
    _ =
      (ξ ⟨i.val - 1, by omega⟩ μ : ℂ) +
        (ξ ⟨i.val, by omega⟩ μ : ℂ) := by
          simpa using hprevμ
    _ =
      ((ξ ⟨i.val - 1, by omega⟩ +
          ξ ⟨i.val, by omega⟩) μ : ℂ) := by simp

omit [NeZero d] in
/-- On the successor reduced difference, the induced real adjacent
transposition adds the selected adjacent difference. -/
theorem realPermOnReducedDiff_adjacentSwap_next
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (hnext : i.val + 2 < m + 1)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ
        ⟨i.val + 1, by omega⟩ =
      ξ ⟨i.val + 1, by omega⟩ + ξ ⟨i.val, by omega⟩ := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        ⟨i.val + 1, by omega⟩)
      μ
  have hnextμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_next
        (d := d) m i hi hnext (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ
        ⟨i.val + 1, by omega⟩ μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) ⟨i.val + 1, by omega⟩ μ := hcomplexμ
    _ =
      (ξ ⟨i.val + 1, by omega⟩ μ : ℂ) +
        (ξ ⟨i.val, by omega⟩ μ : ℂ) := by
          simpa using hnextμ
    _ =
      ((ξ ⟨i.val + 1, by omega⟩ +
          ξ ⟨i.val, by omega⟩) μ : ℂ) := by simp

omit [NeZero d] in
/-- Reduced differences strictly to the left of the adjacent pair are fixed by
the induced real adjacent transposition. -/
theorem realPermOnReducedDiff_adjacentSwap_left_far
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (k : Fin m) (hleft : k.val + 1 < i.val)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ k =
      ξ k := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        k)
      μ
  have hfarμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_left_far
        (d := d) m i hi k hleft (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ k μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) k μ := hcomplexμ
    _ = (ξ k μ : ℂ) := by simpa using hfarμ

omit [NeZero d] in
/-- Reduced differences strictly to the right of the adjacent pair are fixed by
the induced real adjacent transposition. -/
theorem realPermOnReducedDiff_adjacentSwap_right_far
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (k : Fin m) (hright : i.val + 1 < k.val)
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ k =
      ξ k := by
  ext μ
  have hcomplexμ :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
        k)
      μ
  have hfarμ :=
    congrFun
      (permOnReducedDiff_adjacentSwap_right_far
        (d := d) m i hi k hright (fun k μ => (ξ k μ : ℂ)))
      μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ k μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1)
        (Equiv.swap i ⟨i.val + 1, hi⟩)
        (fun k μ => (ξ k μ : ℂ)) k μ := hcomplexμ
    _ = (ξ k μ : ℂ) := by simpa using hfarμ

/-- The induced real adjacent reduced transposition preserves the selected
reduced spacelike edge. -/
theorem realPermOnReducedDiff_adjacentSwap_mem_reducedSpacelikeSwapEdge
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ξ : NPointDomain d m)
    (hξ :
      ξ ∈ reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ∈
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  rw [mem_reducedSpacelikeSwapEdge_adjacent_iff] at hξ ⊢
  have hsel :=
    realPermOnReducedDiff_adjacentSwap_selected
      (d := d) m i hi ξ
  rw [hsel]
  exact (minkowski_isSpacelike_neg_iff (d := d)
    (ξ ⟨i.val, by omega⟩)).2 hξ

omit [NeZero d] in
/-- The real induced reduced permutation action is inverted by the inverse
absolute permutation. -/
theorem realPermOnReducedDiff_symm_apply
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (ξ : NPointDomain d m) :
    realPermOnReducedDiff (d := d) m σ.symm
        (realPermOnReducedDiff (d := d) m σ ξ) = ξ := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  let ξC : BHW.ReducedNPointConfig d m := fun k μ => (ξ k μ : ℂ)
  have hinner :
      (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) =
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ ξC := by
    simpa [ξC] using ofReal_realPermOnReducedDiff_eq (d := d) m σ ξ
  ext k μ
  apply Complex.ofReal_injective
  calc
    (realPermOnReducedDiff (d := d) m σ.symm
        (realPermOnReducedDiff (d := d) m σ ξ) k μ : ℂ)
        =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm
        (fun k μ => (realPermOnReducedDiff (d := d) m σ ξ k μ : ℂ)) k μ := by
          exact congrFun
            (congrFun
              (ofReal_realPermOnReducedDiff_eq
                (d := d) m σ.symm
                (realPermOnReducedDiff (d := d) m σ ξ))
              k)
            μ
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm
        (BHW.permOnReducedDiff (d := d) (n := m + 1) σ ξC) k μ := by
          exact congrFun
            (congrFun
              (congrArg
                (fun η =>
                  BHW.permOnReducedDiff (d := d) (n := m + 1) σ.symm η)
                hinner)
              k)
            μ
    _ =
      BHW.permOnReducedDiff (d := d) (n := m + 1) (σ * σ.symm) ξC k μ := by
          exact congrFun
            (congrFun
              ((BHW.permOnReducedDiff_mul (d := d) (n := m + 1)
                σ σ.symm ξC).symm)
              k)
            μ
    _ = (ξ k μ : ℂ) := by
          have hone :
              BHW.permOnReducedDiff (d := d) (n := m + 1)
                  (1 : Equiv.Perm (Fin (m + 1))) ξC = ξC :=
                BHW.permOnReducedDiff_one (d := d) (n := m + 1) ξC
          simpa [ξC] using congrFun (congrFun hone k) μ

omit [NeZero d] in
/-- The induced real reduced permutation action is continuous. -/
theorem continuous_realPermOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    Continuous (realPermOnReducedDiff (d := d) m σ) := by
  have hcomplexify :
      Continuous (fun ξ : NPointDomain d m =>
        ((fun k μ => (ξ k μ : ℂ)) : BHW.ReducedNPointConfig d m)) := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    exact Complex.continuous_ofReal.comp
      ((continuous_apply μ).comp (continuous_apply k))
  apply continuous_pi
  intro k
  apply continuous_pi
  intro μ
  change Continuous fun ξ : NPointDomain d m =>
    (BHW.permOnReducedDiff (d := d) (n := m + 1) σ
      (fun k μ => (ξ k μ : ℂ)) k μ).re
  exact Complex.continuous_re.comp
    ((continuous_apply μ).comp
      ((continuous_apply k).comp
        ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ).continuous.comp
          hcomplexify)))

omit [NeZero d] in
/-- The induced real reduced permutation action as a homeomorphism. -/
noncomputable def realPermOnReducedDiffHomeomorph
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃ₜ NPointDomain d m where
  toFun := realPermOnReducedDiff (d := d) m σ
  invFun := realPermOnReducedDiff (d := d) m σ.symm
  left_inv := by
    intro ξ
    exact realPermOnReducedDiff_symm_apply (d := d) m σ ξ
  right_inv := by
    intro ξ
    simpa using realPermOnReducedDiff_symm_apply (d := d) m σ.symm ξ
  continuous_toFun := continuous_realPermOnReducedDiff (d := d) m σ
  continuous_invFun := continuous_realPermOnReducedDiff (d := d) m σ.symm

omit [NeZero d] in
/-- The induced real reduced permutation action as a real linear equivalence.

This is the linear/Jacobian package behind the reduced Ruelle change of
variables.  The map is defined through the complex reduced action and then
restricted to real configurations; linearity follows by complexifying the real
test configurations. -/
noncomputable def realPermOnReducedDiffLinearEquiv
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃ₗ[ℝ] NPointDomain d m where
  toFun := realPermOnReducedDiff (d := d) m σ
  invFun := realPermOnReducedDiff (d := d) m σ.symm
  map_add' := by
    intro ξ η
    ext k μ
    have h :=
      congrFun
        (congrFun
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ).map_add
            (fun k μ => (ξ k μ : ℂ))
            (fun k μ => (η k μ : ℂ)))
          k)
        μ
    simpa [realPermOnReducedDiff, Pi.add_apply] using congrArg Complex.re h
  map_smul' := by
    intro a ξ
    ext k μ
    have h :=
      congrFun
        (congrFun
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ).map_smul
            (a : ℂ) (fun k μ => (ξ k μ : ℂ)))
          k)
        μ
    have harg :
        (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) =
          ((a : ℂ) • fun k μ => (ξ k μ : ℂ)) := by
      ext k μ
      simp [Pi.smul_apply]
    change
      ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) k μ).re =
        a *
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ)) k μ).re
    calc
      ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          (fun k μ => (((a • ξ) k μ : ℝ) : ℂ)) k μ).re =
        ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
          ((a : ℂ) • fun k μ => (ξ k μ : ℂ)) k μ).re := by
            exact congrArg
              (fun F =>
                ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ) F k μ).re)
              harg
      _ = (((a : ℂ) •
          (BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ))) k μ).re := by
            exact congrArg Complex.re h
      _ =
        a *
          ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
            (fun k μ => (ξ k μ : ℂ)) k μ).re := by
            change
              (((a : ℂ) *
                ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
                  (fun k μ => (ξ k μ : ℂ)) k μ)).re) =
                a *
                  ((BHW.permOnReducedDiff (d := d) (n := m + 1) σ)
                    (fun k μ => (ξ k μ : ℂ)) k μ).re
            simp
  left_inv := by
    intro ξ
    exact realPermOnReducedDiff_symm_apply (d := d) m σ ξ
  right_inv := by
    intro ξ
    simpa using realPermOnReducedDiff_symm_apply (d := d) m σ.symm ξ

omit [NeZero d] in
/-- The induced real reduced permutation action as a continuous linear
equivalence. -/
noncomputable def realPermOnReducedDiffCLE
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    NPointDomain d m ≃L[ℝ] NPointDomain d m :=
  (realPermOnReducedDiffLinearEquiv (d := d) m σ).toContinuousLinearEquiv

omit [NeZero d] in
/-- The induced real adjacent reduced transposition preserves Lebesgue
measure on reduced coordinates.

This is the Jacobian-one change-of-variables fact needed by the
fiber-marginal Ruelle comparison: the adjacent transposition is an involutive
real linear equivalence, hence its determinant has absolute value `1`. -/
theorem realPermOnReducedDiff_adjacentSwap_measurePreserving
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1) :
    MeasurePreserving
      (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩))
      (volume : Measure (NPointDomain d m))
      (volume : Measure (NPointDomain d m)) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let e : NPointDomain d m ≃ₗ[ℝ] NPointDomain d m :=
    realPermOnReducedDiffLinearEquiv (d := d) m τ
  have hcomp : (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m).comp
        (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
      LinearMap.id := by
    apply LinearMap.ext
    intro ξ
    ext k μ
    change realPermOnReducedDiff (d := d) m τ
        (realPermOnReducedDiff (d := d) m τ ξ) k μ = ξ k μ
    have h :=
      realPermOnReducedDiff_symm_apply (d := d) m τ ξ
    simpa [τ] using congrFun (congrFun h k) μ
  have hdet_sq :
      LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) *
          LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
        1 := by
    have h := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_id] at h
    exact h
  have hdet_abs :
      |LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m)| = 1 := by
    have hpow :
        LinearMap.det (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) ^ 2 =
          1 := by
      simpa [pow_two] using hdet_sq
    rcases sq_eq_one_iff.mp hpow with hdet | hdet <;> simp [hdet]
  have hsymm_eq :
      (e.symm : NPointDomain d m →ₗ[ℝ] NPointDomain d m) =
        (e : NPointDomain d m →ₗ[ℝ] NPointDomain d m) := by
    apply LinearMap.ext
    intro ξ
    ext k μ
    change realPermOnReducedDiff (d := d) m τ.symm ξ k μ =
      realPermOnReducedDiff (d := d) m τ ξ k μ
    simp [τ]
  have hdet_abs_symm :
      |LinearMap.det (e.symm : NPointDomain d m →ₗ[ℝ] NPointDomain d m)| = 1 := by
    rw [hsymm_eq]
    exact hdet_abs
  constructor
  · exact ((realPermOnReducedDiffCLE (d := d) m τ).continuous.measurable)
  · change Measure.map (⇑e) (volume : Measure (NPointDomain d m)) =
      (volume : Measure (NPointDomain d m))
    ext s hs
    have hmeas : Measurable (⇑e : NPointDomain d m → NPointDomain d m) :=
      e.toContinuousLinearEquiv.continuous.measurable
    rw [Measure.map_apply hmeas hs]
    change volume (e ⁻¹' s) = volume s
    rw [Measure.addHaar_preimage_linearEquiv
      (volume : Measure (NPointDomain d m)) e s]
    simp [hdet_abs_symm]

/-- The canonical-after-swap branch is the ordinary canonical branch evaluated
at the induced real reduced permutation of the base point. -/
theorem canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (ε : ℝ) (ξ : NPointDomain d m) :
    canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ =
      canonicalReducedBranch (d := d) OS lgc m ε
        (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ) := by
  simp only [canonicalAfterReducedSwapBranch, canonicalReducedBranch]
  congr 1
  ext k μ
  have h :=
    congrFun
      (congrFun
        (ofReal_realPermOnReducedDiff_eq
          (d := d) m (Equiv.swap i j) ξ)
        k)
      μ
  rw [← h]

/-- Change variables in the canonical-after-adjacent-swap integral.

After the Jacobian-one reduced adjacent transposition, the first term in the
canonical-swap normal form becomes the ordinary canonical branch tested against
the transported reduced test. -/
theorem integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (ε : ℝ) (Φ : NPointDomain d m → ℂ) :
    (∫ ξ : NPointDomain d m,
        canonicalAfterReducedSwapBranch
            (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
          Φ ξ) =
      ∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          Φ (realPermOnReducedDiff (d := d) m
            (Equiv.swap i ⟨i.val + 1, hi⟩) ξ) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let T : NPointDomain d m → NPointDomain d m :=
    realPermOnReducedDiff (d := d) m τ
  let F : NPointDomain d m → ℂ := fun η =>
    canonicalReducedBranch (d := d) OS lgc m ε η * Φ (T η)
  have hmp :=
    realPermOnReducedDiff_adjacentSwap_measurePreserving
      (d := d) m i hi
  calc
    (∫ ξ : NPointDomain d m,
        canonicalAfterReducedSwapBranch
            (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
          Φ ξ)
        =
      ∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε (T ξ) * Φ ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [canonicalAfterReducedSwapBranch_eq_canonicalReducedBranch_realPerm
            (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ]
    _ = ∫ ξ : NPointDomain d m, F (T ξ) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          have hdouble : T (T ξ) = ξ := by
            simpa [T, τ] using
              realPermOnReducedDiff_symm_apply (d := d) m τ ξ
          simp [F, hdouble]
    _ = ∫ ξ : NPointDomain d m, F ξ := by
          have hme : MeasurableEmbedding T := by
            simpa [T] using
              (realPermOnReducedDiffHomeomorph
                (d := d) m τ).toMeasurableEquiv.measurableEmbedding
          exact MeasurePreserving.integral_comp hmp hme F
    _ =
      ∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          Φ (realPermOnReducedDiff (d := d) m
            (Equiv.swap i ⟨i.val + 1, hi⟩) ξ) := by
          simp [F, T, τ]

/-- The canonical-swap reduced fiber difference after the Jacobian-one
adjacent change of variables.

This exposes the remaining Ruelle/Jost payload as distributional invariance of
the ordinary canonical branch under the transported reduced fiber marginal. -/
theorem canonicalSwapReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f : SchwartzNPoint d (m + 1)) (ε : ℝ) :
    canonicalSwapReducedFiberDifference
        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ f ε =
      (∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          reducedFiberMarginal (d := d) m f
            (realPermOnReducedDiff (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) -
      ∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          reducedFiberMarginal (d := d) m f ξ := by
  simp only [canonicalSwapReducedFiberDifference, reducedFiberBranchDifference]
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (reducedFiberMarginal (d := d) m f)]

/-- Adjacent reduced fiber difference in the transported-test canonical
distribution form. -/
theorem adjacentReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f : SchwartzNPoint d (m + 1)) (ε : ℝ) :
    adjacentReducedFiberDifference
        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ f ε =
      (∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          reducedFiberMarginal (d := d) m f
            (realPermOnReducedDiff (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) -
      ∫ ξ : NPointDomain d m,
        canonicalReducedBranch (d := d) OS lgc m ε ξ *
          reducedFiberMarginal (d := d) m f ξ := by
  rw [adjacentReducedFiberDifference_eq_canonicalSwapReducedFiberDifference
    (d := d) OS lgc m i ⟨i.val + 1, hi⟩ f]
  exact
    canonicalSwapReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
      (d := d) OS lgc m i hi f ε

omit [NeZero d] in
/-- Compact support is preserved when a reduced test is precomposed with the
induced real reduced permutation action. -/
theorem hasCompactSupport_comp_realPermOnReducedDiff
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (Φ : NPointDomain d m → ℂ)
    (hΦ : HasCompactSupport Φ) :
    HasCompactSupport
      (fun ξ : NPointDomain d m =>
        Φ (realPermOnReducedDiff (d := d) m σ ξ)) := by
  simpa [Function.comp_def, realPermOnReducedDiffHomeomorph]
    using
      hΦ.comp_homeomorph
        (realPermOnReducedDiffHomeomorph (d := d) m σ)

/-- Precomposing a reduced test supported on the selected adjacent spacelike
edge by the induced real adjacent transposition keeps its support on that same
edge. -/
theorem support_comp_realPermOnReducedDiff_adjacentSwap_subset_edge
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Φ : NPointDomain d m → ℂ)
    (hΦ_support :
      Function.support Φ ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Function.support
        (fun ξ : NPointDomain d m =>
          Φ (realPermOnReducedDiff (d := d) m
            (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  intro ξ hξ
  have hτξ_edge :
      realPermOnReducedDiff (d := d) m
          (Equiv.swap i ⟨i.val + 1, hi⟩) ξ ∈
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ :=
    hΦ_support hξ
  have hback :=
    realPermOnReducedDiff_adjacentSwap_mem_reducedSpacelikeSwapEdge
      (d := d) m i hi
      (realPermOnReducedDiff (d := d) m
        (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)
      hτξ_edge
  have hdouble :
      realPermOnReducedDiff (d := d) m
          (Equiv.swap i ⟨i.val + 1, hi⟩)
          (realPermOnReducedDiff (d := d) m
            (Equiv.swap i ⟨i.val + 1, hi⟩) ξ) = ξ := by
    simpa using
      realPermOnReducedDiff_symm_apply
        (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) ξ
  simpa [hdouble] using hback

/-- The basepoint fiber marginal of an absolute test supported on the selected
adjacent reduced edge remains supported on that edge after precomposition by
the induced real adjacent transposition. -/
theorem reducedFiberMarginal_comp_adjacentSwap_support_subset_edge
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f : SchwartzNPoint d (m + 1))
    (hf_support :
      ∀ x, f.toFun x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    Function.support
        (fun ξ : NPointDomain d m =>
          reducedFiberMarginal (d := d) m f
            (realPermOnReducedDiff (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  have hmargin_support :
      Function.support (reducedFiberMarginal (d := d) m f) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ :=
    reducedFiberIntegral_support_subset_of_absolute_reduced_support
      (d := d) m (f : NPointDomain d (m + 1) → ℂ)
      (reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩)
      hf_support
  simpa [reducedFiberMarginal] using
    support_comp_realPermOnReducedDiff_adjacentSwap_subset_edge
      (d := d) m i hi
      (reducedFiberIntegral (d := d) m
        (f : NPointDomain d (m + 1) → ℂ))
      hmargin_support

/-- If an absolute test has reduced support on the selected adjacent spacelike
edge, then its adjacent-swapped absolute pullback has reduced support on the
same edge. -/
theorem absolute_adjacentSwap_reduced_support_subset_edge
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f : NPointDomain d (m + 1) → ℂ)
    (hf_support :
      ∀ x, f x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    ∀ x,
      f (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  intro x hx
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  have hτ_edge :
      realPermOnReducedDiff (d := d) m τ
          (BHW.reducedDiffMapReal (m + 1) d x) ∈
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
    have hred :=
      hf_support (fun k => x (τ k)) (by simpa [τ] using hx)
    have hperm :=
      reducedDiffMapReal_permute_absolute (d := d) m τ x
    simpa [τ] using hperm ▸ hred
  have hback :=
    realPermOnReducedDiff_adjacentSwap_mem_reducedSpacelikeSwapEdge
      (d := d) m i hi
      (realPermOnReducedDiff (d := d) m τ
        (BHW.reducedDiffMapReal (m + 1) d x))
      (by simpa [τ] using hτ_edge)
  have hdouble :
      realPermOnReducedDiff (d := d) m τ
          (realPermOnReducedDiff (d := d) m τ
            (BHW.reducedDiffMapReal (m + 1) d x)) =
        BHW.reducedDiffMapReal (m + 1) d x := by
    simpa [τ] using
      realPermOnReducedDiff_symm_apply
        (d := d) m τ (BHW.reducedDiffMapReal (m + 1) d x)
  exact hdouble ▸ hback

/-- Canonical reduced compact-edge boundary invariance under the induced
adjacent reduced real transposition.

This is the remaining analytic/Jost-Ruelle payload after the finite-dimensional
reduced transport has been paid.  The hypothesis is distributional: it is an
integral statement for every compact reduced test supported on the selected
adjacent spacelike edge. -/
def ReducedCanonicalAdjacentSwapBoundaryInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (Φ : NPointDomain d m → ℂ),
    HasCompactSupport Φ →
    Function.support Φ ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ *
            Φ (realPermOnReducedDiff (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * Φ ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

/-- Fiber-marginal form of the adjacent reduced Ruelle/Jost distributional
limit.

This is the reduced-variable theorem left after quotienting out the arbitrary
absolute basepoint.  It is still the genuine Ruelle/Jost analytic payload: the
test function is the basepoint fiber marginal of the original compact absolute
test. -/
def AdjacentReducedRuelleFiberMarginalLimit
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
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i ⟨i.val + 1, hi⟩) k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) -
          ∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

/-- The canonical compact-edge boundary-invariance theorem is exactly strong
enough to close the current fiber-marginal Ruelle/Jost blocker. -/
theorem adjacentReducedRuelleFiberMarginalLimit_of_canonicalBoundaryInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hcanon :
      ReducedCanonicalAdjacentSwapBoundaryInvariant (d := d) OS lgc) :
    AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let Φ : NPointDomain d m → ℂ := reducedFiberMarginal (d := d) m f
  have hΦ_compact : HasCompactSupport Φ := by
    simpa [Φ, reducedFiberMarginal] using
      reducedFiberIntegral_hasCompactSupport
        (d := d) m (f : NPointDomain d (m + 1) → ℂ) hf_compact
  have hΦ_support :
      Function.support Φ ⊆
        reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [Φ, reducedFiberMarginal, j] using
      reducedFiberIntegral_support_subset_of_absolute_reduced_support
        (d := d) m (f : NPointDomain d (m + 1) → ℂ)
        (reducedSpacelikeSwapEdge (d := d) m i j)
        hsupport
  have hcanonical :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              Φ (realPermOnReducedDiff (d := d) m
                (Equiv.swap i j) ξ)) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * Φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [j] using hcanon m i hi Φ hΦ_compact hΦ_support
  have htransport :
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) -
          ∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ *
            Φ (realPermOnReducedDiff (d := d) m
              (Equiv.swap i j) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * Φ ξ) := by
    filter_upwards with ε
    simpa [j, Φ, reducedFiberMarginal] using
      adjacentReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
        (d := d) OS lgc m i hi f ε
  exact Filter.Tendsto.congr' htransport.symm hcanonical

/-- The fiber-marginal Ruelle/Jost theorem implies the production absolute-test
adjacent reduced Ruelle/Jost theorem. -/
theorem adjacentReducedRuelleDistributionalLimit_of_fiberMarginal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hfiber :
      AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc) :
    AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let Gperm : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε *
            permutedCanonicalReducedDirectionC
              (d := d) m (Equiv.swap i j) k μ *
            Complex.I)
  let Gcan : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    bvt_F_reduced (d := d) OS lgc m
      (fun k μ =>
        (ξ k μ : ℂ) +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I)
  have hperm_int :
      ∀ᶠ (ε : ℝ) in l,
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            Gperm ε (BHW.reducedDiffMapReal (m + 1) d x) *
              (f x)) volume := by
    simpa [l, Gperm, j] using
      bvt_F_reduced_permuted_integrable_eventually
        (d := d) OS lgc m i j f
  have hcan_int :
      ∀ᶠ (ε : ℝ) in l,
        Integrable
          (fun x : NPointDomain d (m + 1) =>
            Gcan ε (BHW.reducedDiffMapReal (m + 1) d x) *
              (f x)) volume := by
    simpa [l, Gcan] using
      bvt_F_reduced_canonical_integrable_eventually
        (d := d) OS lgc m f
  have heq :
      (fun ε : ℝ =>
        (∫ x : NPointDomain d (m + 1),
            Gperm ε (BHW.reducedDiffMapReal (m + 1) d x) * (f x)) -
          ∫ x : NPointDomain d (m + 1),
            Gcan ε (BHW.reducedDiffMapReal (m + 1) d x) * (f x))
        =ᶠ[l]
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
            Gperm ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) -
          ∫ ξ : NPointDomain d m,
            Gcan ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) := by
    filter_upwards [hperm_int, hcan_int] with ε hpermε hcanε
    rw [integral_reducedFiberIntegral_eq (d := d) m
        (f : NPointDomain d (m + 1) → ℂ) (Gperm ε) hpermε]
    rw [integral_reducedFiberIntegral_eq (d := d) m
        (f : NPointDomain d (m + 1) → ℂ) (Gcan ε) hcanε]
  have hfiber' :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
              Gperm ε ξ *
                reducedFiberIntegral (d := d) m
                  (f : NPointDomain d (m + 1) → ℂ) ξ) -
            ∫ ξ : NPointDomain d m,
              Gcan ε ξ *
                reducedFiberIntegral (d := d) m
                  (f : NPointDomain d (m + 1) → ℂ) ξ)
        l (nhds 0) := by
    simpa [AdjacentReducedRuelleFiberMarginalLimit, Gperm, Gcan, j, l]
      using hfiber m i hi f hf_compact hsupport
  simpa [Gperm, Gcan, j, l] using
    (Filter.Tendsto.congr' heq.symm hfiber')

end OSReconstruction
