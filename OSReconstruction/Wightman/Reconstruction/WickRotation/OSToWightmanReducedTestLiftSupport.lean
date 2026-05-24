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
