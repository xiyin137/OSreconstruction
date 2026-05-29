import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedCanonicalBoundaryCLM
import OSReconstruction.Wightman.SpectralEquivalence

/-!
# Reduced Fiber Marginals as Schwartz Reductions

This small bridge identifies the theorem-2 reduced fiber marginal with the
existing Schwartz-space `diffVarReduction`.  It keeps the book-style
test-function formulation separate from the main reduced transport file.
-/

open MeasureTheory Filter

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The full real difference-coordinate inverse with a prepended basepoint is
the same absolute configuration as the standard zero-basepoint difference
section translated by that basepoint. -/
theorem realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
    (m : ℕ) (x₀ : SpacetimeDim d) (ξ : NPointDomain d m) :
    (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ) =
      fun k μ => x₀ μ + diffVarSection d m ξ k μ := by
  ext k μ
  induction k using Fin.induction with
  | zero =>
      simp [diffVarSection_zero]
  | succ k ih =>
      have hred :=
        congrFun
          (congrFun
            (BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
              (d := d) (m := m) x₀ ξ) k) μ
      rw [BHW.reducedDiffMapReal_apply] at hred
      have hstep :
          (BHW.realDiffCoordCLE (m + 1) d).symm
              (BHW.prependBasepointReal d m x₀ ξ) k.succ μ =
            (BHW.realDiffCoordCLE (m + 1) d).symm
              (BHW.prependBasepointReal d m x₀ ξ) k.castSucc μ +
              ξ k μ := by
        simpa [add_comm] using (eq_add_of_sub_eq hred)
      rw [hstep, ih]
      rw [diffVarSection_succ]
      ring

/-- The basepoint fiber marginal of an absolute Schwartz test is precisely the
existing Schwartz-space difference-variable reduction. -/
theorem reducedFiberMarginal_eq_diffVarReduction
    (m : ℕ) (f : SchwartzNPoint d (m + 1)) :
    reducedFiberMarginal (d := d) m f =
      (diffVarReduction d m f : NPointDomain d m → ℂ) := by
  funext ξ
  change
    reducedFiberIntegral (d := d) m
        (f : NPointDomain d (m + 1) → ℂ) ξ =
      diffVarReduction d m f ξ
  simp only [reducedFiberIntegral, diffVarReduction]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x₀
  congr 1
  exact
    realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
      (d := d) m x₀ ξ

/-- After an absolute permutation of a reduced test lift, integrating out the
basepoint cutoff leaves exactly the induced reduced permutation of the
reduced test. -/
theorem reducedFiberMarginal_absPerm_reducedTestLift_eq
    (m : ℕ) (σ : Equiv.Perm (Fin (m + 1)))
    (χ : BHW.NormalizedBasepointCutoff d) (φ : SchwartzNPoint d m) :
    reducedFiberMarginal (d := d) m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
          (BHW.reducedTestLift m d χ.toSchwartz φ)) =
      fun ξ => φ (realPermOnReducedDiff (d := d) m σ ξ) := by
  funext ξ
  let fσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
      (BHW.reducedTestLift m d χ.toSchwartz φ)
  let c : SpacetimeDim d := diffVarSection d m ξ (σ 0)
  have hpoint :
      ∀ x₀ : SpacetimeDim d,
        fσ ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) =
          χ.toSchwartz (x₀ + c) *
            φ (realPermOnReducedDiff (d := d) m σ ξ) := by
    intro x₀
    let y : NPointDomain d (m + 1) :=
      (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ)
    have hred :
        BHW.reducedDiffMapReal (m + 1) d (fun k => y (σ k)) =
          realPermOnReducedDiff (d := d) m σ ξ := by
      simpa [y] using
        reducedDiffMapReal_permute_realDiffCoordCLE_symm_prependBasepointReal
          (d := d) m σ x₀ ξ
    have hbase : y (σ 0) = x₀ + c := by
      ext μ
      have h :=
        congrFun
          (congrFun
            (realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
              (d := d) m x₀ ξ)
            (σ 0))
          μ
      simpa [y, c, Pi.add_apply] using h
    change BHW.reducedTestLift m d χ.toSchwartz φ (fun k => y (σ k)) =
      χ.toSchwartz (x₀ + c) *
        φ (realPermOnReducedDiff (d := d) m σ ξ)
    rw [BHW.reducedTestLift_apply]
    rw [hbase, hred]
  have hχ_shift :
      ∫ x₀ : SpacetimeDim d, χ.toSchwartz (x₀ + c) = 1 := by
    calc
      (∫ x₀ : SpacetimeDim d, χ.toSchwartz (x₀ + c))
          = ∫ x₀ : SpacetimeDim d, χ.toSchwartz x₀ := by
            simpa using
              (MeasureTheory.integral_add_right_eq_self
                (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                (fun x₀ : SpacetimeDim d => χ.toSchwartz x₀) c)
      _ = 1 := χ.integral_eq_one
  change
    reducedFiberIntegral (d := d) m
        (fσ : NPointDomain d (m + 1) → ℂ) ξ =
      φ (realPermOnReducedDiff (d := d) m σ ξ)
  simp only [reducedFiberIntegral]
  simp_rw [hpoint]
  have hfun :
      (fun x₀ : SpacetimeDim d =>
          χ.toSchwartz (x₀ + c) *
            φ (realPermOnReducedDiff (d := d) m σ ξ)) =
        fun x₀ : SpacetimeDim d =>
          (φ (realPermOnReducedDiff (d := d) m σ ξ)) •
            χ.toSchwartz (x₀ + c) := by
    ext x₀
    simp [smul_eq_mul, mul_comm]
  rw [hfun, MeasureTheory.integral_smul, hχ_shift]
  simp [smul_eq_mul]

omit [NeZero d] in
/-- After integrating out the basepoint, an absolute permutation of an
arbitrary absolute test descends to the induced reduced permutation.

This is the coordinate algebra behind the reduced locality route: absolute
adjacent swaps act on the fiber marginal only through
`realPermOnReducedDiff`. -/
theorem reducedFiberMarginal_absPerm_eq
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (f : SchwartzNPoint d (m + 1)) :
    reducedFiberMarginal (d := d) m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
          f) =
      fun ξ =>
        reducedFiberMarginal (d := d) m f
          (realPermOnReducedDiff (d := d) m σ ξ) := by
  funext ξ
  let fσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
      f
  let η : NPointDomain d m := realPermOnReducedDiff (d := d) m σ ξ
  let c : SpacetimeDim d := diffVarSection d m ξ (σ 0)
  have hpoint :
      ∀ x₀ : SpacetimeDim d,
        fσ ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ ξ)) =
        f ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m (x₀ + c) η)) := by
    intro x₀
    let y : NPointDomain d (m + 1) :=
      (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m x₀ ξ)
    let z : NPointDomain d (m + 1) :=
      (BHW.realDiffCoordCLE (m + 1) d).symm
        (BHW.prependBasepointReal d m (x₀ + c) η)
    have hred :
        BHW.reducedDiffMapReal (m + 1) d (fun k => y (σ k)) = η := by
      simpa [y, η] using
        reducedDiffMapReal_permute_realDiffCoordCLE_symm_prependBasepointReal
          (d := d) m σ x₀ ξ
    have hbase : y (σ 0) = x₀ + c := by
      ext μ
      have h :=
        congrFun
          (congrFun
            (realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
              (d := d) m x₀ ξ)
            (σ 0))
          μ
      simpa [y, c, Pi.add_apply] using h
    have hz_base : z 0 = x₀ + c := by
      ext μ
      simp [z]
    have hz_red :
        BHW.reducedDiffMapReal (m + 1) d z = η := by
      simpa [z] using
        BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
          (d := d) (m := m) (x₀ := x₀ + c) (ξ := η)
    have hperm_eq_z : (fun k => y (σ k)) = z := by
      apply (BHW.realDiffCoordCLE (m + 1) d).injective
      ext k μ
      by_cases hk : k.val = 0
      · have hk0 : k = 0 := Fin.ext hk
        subst hk0
        simp [BHW.realDiffCoordCLE_apply, hbase, hz_base]
      · rw [BHW.realDiffCoordCLE_apply, BHW.realDiffCoordCLE_apply]
        simp [hk]
        let j : Fin m := ⟨k.val - 1, by omega⟩
        have hk_succ : k = j.succ := by
          apply Fin.ext
          simp [j]
          omega
        have hleft :=
          congrFun (congrFun hred j) μ
        have hright :=
          congrFun (congrFun hz_red j) μ
        rw [hk_succ]
        change y (σ j.succ) μ - y (σ j.castSucc) μ =
          z j.succ μ - z j.castSucc μ
        simpa [BHW.reducedDiffMapReal_apply] using hleft.trans hright.symm
    change f (fun k => y (σ k)) = f z
    rw [hperm_eq_z]
  change
    reducedFiberIntegral (d := d) m
        (fσ : NPointDomain d (m + 1) → ℂ) ξ =
      reducedFiberIntegral (d := d) m
        (f : NPointDomain d (m + 1) → ℂ) η
  simp only [reducedFiberIntegral]
  simp_rw [hpoint]
  exact
    MeasureTheory.integral_add_right_eq_self
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
      (fun x₀ : SpacetimeDim d =>
        f ((BHW.realDiffCoordCLE (m + 1) d).symm
          (BHW.prependBasepointReal d m x₀ η)))
      c

/-- Difference-variable reduction commutes with absolute permutations, after
descending the permutation to reduced coordinates. -/
theorem diffVarReduction_absPerm_eq
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (f : SchwartzNPoint d (m + 1)) :
    diffVarReduction d m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
          f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realPermOnReducedDiffCLE (d := d) m σ)
        (diffVarReduction d m f) := by
  apply DFunLike.ext
  intro ξ
  let fσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
      f
  have hmargin := reducedFiberMarginal_absPerm_eq (d := d) m σ f
  have hleft := reducedFiberMarginal_eq_diffVarReduction (d := d) m fσ
  have hright := reducedFiberMarginal_eq_diffVarReduction (d := d) m f
  calc
    diffVarReduction d m fσ ξ =
        reducedFiberMarginal (d := d) m fσ ξ := by
          exact (congrFun hleft ξ).symm
    _ =
        reducedFiberMarginal (d := d) m f
          (realPermOnReducedDiff (d := d) m σ ξ) := by
          simpa [fσ] using congrFun hmargin ξ
    _ =
        diffVarReduction d m f
          (realPermOnReducedDiff (d := d) m σ ξ) := by
          exact congrFun hright _
    _ =
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m σ)
          (diffVarReduction d m f)) ξ := by
          simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
            realPermOnReducedDiffCLE, realPermOnReducedDiffLinearEquiv]

/-- Translation invariance makes the absolute Wightman boundary value depend
only on the fiber marginal/difference-variable reduction.

This is the distributional reduction step from the classical OS/Jost route:
the basepoint direction is integrated out before the adjacent locality
comparison is made on reduced variables. -/
theorem bvt_W_eq_reducedWightmanCLM_diffVarReduction
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (f : SchwartzNPoint d (m + 1)) :
    bvt_W OS lgc (m + 1) f =
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
        (diffVarReduction d m f) := by
  let W : (n : ℕ) → SchwartzNPointSpace d n → ℂ :=
    fun n f => bvt_W OS lgc n f
  obtain ⟨w, _hw_cont, _hw_lin, hw_det⟩ :=
    exists_diffVar_distribution (d := d) (W := W)
      (fun n => bvt_W_continuous (d := d) OS lgc n)
      (fun n => bvt_W_linear (d := d) OS lgc n)
      (fun n a f g hfg =>
        bvt_translation_invariant (d := d) OS lgc n a f g hfg)
      m
  have hf_det :
      bvt_W OS lgc (m + 1) f = w (diffVarReduction d m f) := by
    simpa [W] using hw_det f
  have hlift_reduction :
      diffVarReduction d m
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) =
        diffVarReduction d m f := by
    have hmargin :=
      reducedFiberMarginal_reducedTestLift_eq
        (d := d) m χ (diffVarReduction d m f)
    have hdiff :=
      reducedFiberMarginal_eq_diffVarReduction
        (d := d) m
        (BHW.reducedTestLift m d χ.toSchwartz
          (diffVarReduction d m f))
    apply DFunLike.ext
    intro ξ
    calc
      diffVarReduction d m
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) ξ =
          reducedFiberMarginal (d := d) m
            (BHW.reducedTestLift m d χ.toSchwartz
              (diffVarReduction d m f)) ξ := by
            exact (congrFun hdiff ξ).symm
      _ = diffVarReduction d m f ξ := by
            exact congrFun hmargin ξ
  have hlift_det :
      bvt_W OS lgc (m + 1)
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) =
        w (diffVarReduction d m f) := by
    simpa [W, hlift_reduction] using
      hw_det
        (BHW.reducedTestLift m d χ.toSchwartz
          (diffVarReduction d m f))
  calc
    bvt_W OS lgc (m + 1) f = w (diffVarReduction d m f) := hf_det
    _ =
        bvt_W OS lgc (m + 1)
          (BHW.reducedTestLift m d χ.toSchwartz
            (diffVarReduction d m f)) := hlift_det.symm
    _ =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (diffVarReduction d m f) := by
          rfl

/-- The boundary-value reduction after an absolute permutation of a reduced
test lift: the absolute permutation descends to the induced reduced
permutation. -/
theorem bvt_W_absPerm_reducedTestLift_eq_reducedWightmanCLM_perm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (φ : SchwartzNPoint d m) :
    bvt_W OS lgc (m + 1)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
          (BHW.reducedTestLift m d χ.toSchwartz φ)) =
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m σ) φ) := by
  let fσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
      (BHW.reducedTestLift m d χ.toSchwartz φ)
  have hfactor :
      bvt_W OS lgc (m + 1) fσ =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (diffVarReduction d m fσ) :=
    bvt_W_eq_reducedWightmanCLM_diffVarReduction
      (d := d) OS lgc χ m fσ
  have hred :
      diffVarReduction d m fσ =
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m σ) φ := by
    apply DFunLike.ext
    intro ξ
    have hmargin :=
      reducedFiberMarginal_absPerm_reducedTestLift_eq
        (d := d) m σ χ φ
    have hdiff := reducedFiberMarginal_eq_diffVarReduction (d := d) m fσ
    calc
      diffVarReduction d m fσ ξ =
          reducedFiberMarginal (d := d) m fσ ξ := by
            exact (congrFun hdiff ξ).symm
      _ = φ (realPermOnReducedDiff (d := d) m σ ξ) := by
            simpa [fσ] using congrFun hmargin ξ
      _ =
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m σ) φ) ξ := by
            simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
              realPermOnReducedDiffCLE, realPermOnReducedDiffLinearEquiv]
  simpa [fσ, hred] using hfactor

/-- Arbitrary absolute permutation handoff for boundary values: the absolute
side is reduced to the induced reduced permutation acting on
`diffVarReduction f`. -/
theorem bvt_W_absPerm_eq_reducedWightmanCLM_diffVarReduction_perm
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (σ : Equiv.Perm (Fin (m + 1)))
    (f : SchwartzNPoint d (m + 1)) :
    bvt_W OS lgc (m + 1)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
          f) =
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m σ)
          (diffVarReduction d m f)) := by
  let fσ : SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) σ).toContinuousLinearEquiv)
      f
  have hfactor :
      bvt_W OS lgc (m + 1) fσ =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (diffVarReduction d m fσ) :=
    bvt_W_eq_reducedWightmanCLM_diffVarReduction
      (d := d) OS lgc χ m fσ
  have hred :
      diffVarReduction d m fσ =
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (realPermOnReducedDiffCLE (d := d) m σ)
          (diffVarReduction d m f) := by
    simpa [fσ] using diffVarReduction_absPerm_eq (d := d) m σ f
  simpa [fσ, hred] using hfactor

/-- Compact adjacent locality reduces directly to the reduced boundary-CLM
invariance on the fiber marginal `diffVarReduction f`.

This is the exact bridge from the public absolute Wightman statement to the
remaining reduced Jost/Ruelle boundary-CLM invariant. -/
theorem bvt_W_adjacent_swap_of_reducedBoundaryCLM_invariant_compact
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hinv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (f g : SchwartzNPoint d (m + 1))
    (hf_compact : HasCompactSupport (f : NPointDomain d (m + 1) → ℂ))
    (hsp : ∀ x, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d
        (x i) (x ⟨i.val + 1, hi⟩))
    (hswap : ∀ x, g.toFun x =
      f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) :
    bvt_W OS lgc (m + 1) f = bvt_W OS lgc (m + 1) g := by
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let P : SchwartzNPoint d (m + 1) →L[ℂ] SchwartzNPoint d (m + 1) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) τ).toContinuousLinearEquiv)
  have hg_eq : g = P f := by
    ext x
    exact hswap x
  let φ : SchwartzNPoint d m := diffVarReduction d m f
  have hφ_eq :
      (φ : NPointDomain d m → ℂ) =
        reducedFiberMarginal (d := d) m f := by
    exact (reducedFiberMarginal_eq_diffVarReduction (d := d) m f).symm
  have hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ) := by
    rw [hφ_eq]
    simpa [reducedFiberMarginal] using
      reducedFiberIntegral_hasCompactSupport
        (d := d) m (f : NPointDomain d (m + 1) → ℂ) hf_compact
  have hred_support :
      ∀ x, f.toFun x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
    intro x hx
    exact
      reducedDiffMapReal_mem_reducedSpacelikeSwapEdge_of_areSpacelikeSeparated
        (d := d) m i j x (hsp x hx)
  have hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i j := by
    rw [hφ_eq]
    simpa [reducedFiberMarginal] using
      reducedFiberIntegral_support_subset_of_absolute_reduced_support
        (d := d) m (f : NPointDomain d (m + 1) → ℂ)
        (reducedSpacelikeSwapEdge (d := d) m i j)
        hred_support
  have hleft :
      bvt_W OS lgc (m + 1) f =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m φ := by
    simpa [φ] using
      bvt_W_eq_reducedWightmanCLM_diffVarReduction
        (d := d) OS lgc χ m f
  have hright :
      bvt_W OS lgc (m + 1) g =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m τ) φ) := by
    rw [hg_eq]
    simpa [P, τ, φ] using
      bvt_W_absPerm_eq_reducedWightmanCLM_diffVarReduction_perm
        (d := d) OS lgc χ m τ f
  have hred_eq :
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m τ) φ) =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m φ := by
    simpa [τ, j] using hinv m i hi φ hφ_compact (by simpa [j] using hφ_support)
  calc
    bvt_W OS lgc (m + 1) f =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m φ := hleft
    _ =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m τ) φ) := hred_eq.symm
    _ = bvt_W OS lgc (m + 1) g := hright.symm

/-- Full adjacent locality follows from reduced boundary-CLM invariance.

This is the public theorem-2 consumer after the reduced distributional
boundary equality has been proved: compact tests are reduced through
`diffVarReduction`, and the existing compact-support approximation removes the
compactness hypothesis without changing the ordinary spacelike support
condition. -/
theorem bvt_W_adjacent_swap_of_reducedBoundaryCLM_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hinv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ) :
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
        bv_local_commutativity_full_of_compact_support_adjacent_locality
          (d := d) (W_n := bvt_W OS lgc (m + 1))
          (hW_cont := bvt_W_continuous (d := d) OS lgc (m + 1))
          i hi
          (by
            intro f g hf_compact hsp hswap
            exact
              bvt_W_adjacent_swap_of_reducedBoundaryCLM_invariant_compact
                (d := d) OS lgc χ hinv m i hi f g hf_compact hsp hswap)
          f g hsp hswap

/-- Canonical reduced compact-edge boundary invariance for Schwartz reduced
tests.

This is the book/Jost-Ruelle theorem surface actually needed by theorem 2:
the reduced tests produced from absolute Schwartz functions are themselves
Schwartz functions, not arbitrary compact functions. -/
def ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m),
    HasCompactSupport (φ : NPointDomain d m → ℂ) →
    Function.support (φ : NPointDomain d m → ℂ) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ *
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

/-- Closed-support form of the reduced canonical adjacent-swap boundary
invariant.

This is the support convention used in the local Jost/Ruelle smearing step:
the local mixed-tube packets are applied on neighborhoods of the topological
support, not merely on the nonzero set. -/
def ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m),
    HasCompactSupport (φ : NPointDomain d m → ℂ) →
    tsupport (φ : NPointDomain d m → ℂ) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ *
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

omit [NeZero d] in
theorem hasCompactSupport_prependField_spacetime
    {m : ℕ}
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m)
    (hχ : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hφ : HasCompactSupport (φ : NPointDomain d m → ℂ)) :
    HasCompactSupport
      ((χ.prependField φ : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) → ℂ) := by
  let K : Set (NPointDomain d (m + 1)) :=
    (fun p : SpacetimeDim d × NPointDomain d m =>
      (Fin.cons p.1 p.2 : NPointDomain d (m + 1))) ''
      (tsupport (χ : SpacetimeDim d → ℂ) ×ˢ
        tsupport (φ : NPointDomain d m → ℂ))
  have hKcompact : IsCompact K := by
    have hcont :
        Continuous
          (fun p : SpacetimeDim d × NPointDomain d m =>
            (Fin.cons p.1 p.2 : NPointDomain d (m + 1))) := by
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · exact continuous_fst
      · intro i
        simpa using (continuous_apply i).comp continuous_snd
    simpa [K] using (hχ.isCompact.prod hφ.isCompact).image hcont
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hχx : χ (x 0) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  have hφx : φ (fun i : Fin m => x i.succ) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  refine ⟨(x 0, fun i : Fin m => x i.succ), ?_, ?_⟩
  · exact ⟨subset_tsupport _ (Function.mem_support.mpr hχx),
      subset_tsupport _ (Function.mem_support.mpr hφx)⟩
  · ext j μ
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i
      simp

omit [NeZero d] in
theorem reducedTestLift_hasCompactSupport
    {m : ℕ}
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m)
    (hχ : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hφ : HasCompactSupport (φ : NPointDomain d m → ℂ)) :
    HasCompactSupport
      ((BHW.reducedTestLift m d χ φ : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) → ℂ) := by
  have hpre :
      HasCompactSupport
        ((χ.prependField φ : SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → ℂ) :=
    hasCompactSupport_prependField_spacetime
      (d := d) χ φ hχ hφ
  have hcomp :=
    hpre.comp_homeomorph
      (BHW.realDiffCoordCLE (m + 1) d).toHomeomorph
  simpa [BHW.reducedTestLift, Function.comp,
    SchwartzMap.prependFieldCLMRight_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hcomp

omit [NeZero d] in
theorem reducedTestLift_reduced_support_subset
    {m : ℕ} (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m)
    (hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩) :
    ∀ x, (BHW.reducedTestLift m d χ φ).toFun x ≠ 0 →
      BHW.reducedDiffMapReal (m + 1) d x ∈
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ := by
  intro x hx
  have hφ_ne :
      (φ : NPointDomain d m → ℂ)
        (BHW.reducedDiffMapReal (m + 1) d x) ≠ 0 := by
    intro hzero
    apply hx
    change BHW.reducedTestLift m d χ φ x = 0
    rw [BHW.reducedTestLift_apply]
    rw [mul_eq_zero]
    exact Or.inr hzero
  exact hφ_support hφ_ne

/-- The Schwartz-test canonical boundary invariant is enough for the current
fiber-marginal Ruelle/Jost blocker.

The point of this bridge is that the fiber marginal of an absolute Schwartz
test is exactly `diffVarReduction`, so the remaining analytic theorem can be
proved on the Schwartz test space from the classical Jost/Ruelle argument. -/
theorem adjacentReducedRuelleFiberMarginalLimit_of_canonicalBoundaryInvariantSchwartz
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hcanon :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz
        (d := d) OS lgc) :
    AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc := by
  intro m i hi f hf_compact hsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let φ : SchwartzNPoint d m := diffVarReduction d m f
  have hφ_eq :
      (φ : NPointDomain d m → ℂ) =
        reducedFiberMarginal (d := d) m f := by
    exact (reducedFiberMarginal_eq_diffVarReduction (d := d) m f).symm
  have hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ) := by
    rw [hφ_eq]
    simpa [reducedFiberMarginal] using
      reducedFiberIntegral_hasCompactSupport
        (d := d) m (f : NPointDomain d (m + 1) → ℂ) hf_compact
  have hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i j := by
    rw [hφ_eq]
    simpa [reducedFiberMarginal, j] using
      reducedFiberIntegral_support_subset_of_absolute_reduced_support
        (d := d) m (f : NPointDomain d (m + 1) → ℂ)
        (reducedSpacelikeSwapEdge (d := d) m i j)
        hsupport
  have hcanonical :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              (φ : NPointDomain d m → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ)) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [j] using hcanon m i hi φ hφ_compact hφ_support
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
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ) := by
    filter_upwards with ε
    simpa [j, φ, hφ_eq, reducedFiberMarginal] using
      adjacentReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
        (d := d) OS lgc m i hi f ε
  exact Filter.Tendsto.congr' htransport.symm hcanonical

private theorem exists_finite_schwartz_partitionOfUnity_on_compact_openCover
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let V : α → Set E := fun i => U i ∩ Metric.ball (0 : E) (R + 1)
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact (hU_open i).inter Metric.isOpen_ball
  have hV_relcompact : ∀ i, ∃ c r, V i ⊆ Metric.closedBall c r := by
    intro i
    refine ⟨(0 : E), R + 1, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hV_cover : K ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxR : dist x (0 : E) ≤ R := by
      simpa [dist_comm] using Metric.mem_closedBall.mp (hR hx)
    have hxball : x ∈ Metric.ball (0 : E) (R + 1) := by
      rw [Metric.mem_ball]
      linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, hxball⟩⟩
  obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      (E := E) hK hV_open hV_relcompact hV_cover
  refine ⟨χ, hχ_compact, ?_, hχ_sum⟩
  intro i
  exact (hχ_sub i).trans Set.inter_subset_left

private theorem canonicalReducedBranch_integrable_of_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ)) :
    Integrable
      (fun ξ : NPointDomain d m =>
        canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ) volume := by
  let H : NPointDomain d m → ℂ := fun ξ =>
    canonicalReducedBranch (d := d) OS lgc m ε ξ
  have harg_cont :
      Continuous
        (fun ξ : NPointDomain d m =>
          fun k μ =>
            (ξ k μ : ℂ) +
              ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
    fun_prop
  have hH_cont : ContinuousOn H Set.univ := by
    refine
      (bvt_F_reduced_holomorphicOn_reducedForwardTube
        (d := d) OS lgc m).continuousOn.comp harg_cont.continuousOn ?_
    intro ξ _hξ
    exact reducedCanonicalApproach_mem_reducedForwardTube
      (d := d) m ξ hε
  exact
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (H := H) (ψ := φ) (U := Set.univ)
      isOpen_univ hH_cont ⟨hφ_compact, by intro ξ hξ; trivial⟩

private theorem canonicalAfterReducedSwapBranch_integrable_of_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1)) (ε : ℝ) (hε : 0 < ε)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ)) :
    Integrable
      (fun ξ : NPointDomain d m =>
        canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ *
          φ ξ) volume := by
  let H : NPointDomain d m → ℂ := fun ξ =>
    canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let T : NPointDomain d m → NPointDomain d m :=
    realPermOnReducedDiff (d := d) m σ
  have hofReal_cont :
      Continuous
        (fun ξ : NPointDomain d m =>
          ((fun k μ => (ξ k μ : ℂ)) : BHW.ReducedNPointConfig d m)) := by
    fun_prop
  have hperm_cont :
      Continuous
        (fun ξ : NPointDomain d m =>
          BHW.permOnReducedDiff (d := d) (n := m + 1) σ
            (fun k μ => (ξ k μ : ℂ))) :=
    (BHW.permOnReducedDiff (d := d) (n := m + 1) σ).continuous.comp
      hofReal_cont
  have harg_cont :
      Continuous
        (fun ξ : NPointDomain d m =>
          fun k μ =>
            BHW.permOnReducedDiff (d := d) (n := m + 1) σ
                (fun k μ => (ξ k μ : ℂ)) k μ +
              ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) := by
    simpa [Pi.add_apply] using
      hperm_cont.add
        (continuous_const :
          Continuous
            (fun _ : NPointDomain d m =>
              fun k μ =>
                (ε : ℂ) *
                  canonicalReducedDirectionC (d := d) m k μ * Complex.I))
  have hH_cont : ContinuousOn H Set.univ := by
    refine
      (bvt_F_reduced_holomorphicOn_reducedForwardTube
        (d := d) OS lgc m).continuousOn.comp harg_cont.continuousOn ?_
    intro ξ _hξ
    have hmem :=
      reducedCanonicalApproach_mem_reducedForwardTube
        (d := d) m (T ξ) hε
    change
      (fun k μ =>
        BHW.permOnReducedDiff (d := d) (n := m + 1) σ
            (fun k μ => (ξ k μ : ℂ)) k μ +
          ε * canonicalReducedDirectionC (d := d) m k μ * Complex.I) ∈
        BHW.ReducedForwardTubeN d m
    rw [← ofReal_realPermOnReducedDiff_eq (d := d) m σ ξ]
    exact hmem
  exact
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (H := H) (ψ := φ) (U := Set.univ)
      isOpen_univ hH_cont ⟨hφ_compact, by intro ξ hξ; trivial⟩

/-- Reduced-domain DCT for the adjacent-after-swap branch minus the canonical
reduced branch.

The genuine Jost/Ruelle input is `hpointwise` plus the collar domination
packet.  This lemma only performs the measure-theoretic passage from those
inputs to the compact-test integral limit. -/
theorem reduced_domain_two_branch_integral_tendsto_zero_of_support_pointwise_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i j : Fin (m + 1))
    (φ : SchwartzNPoint d m)
    (hpointwise :
      ∀ ξ, φ ξ ≠ 0 →
        Filter.Tendsto
          (fun ε : ℝ =>
            canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ -
              canonicalReducedBranch (d := d) OS lgc m ε ξ)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
          (nhds 0))
    (bound : NPointDomain d m → ℝ)
    (hF_meas :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        AEStronglyMeasurable
          (fun ξ : NPointDomain d m =>
            (canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ -
              canonicalReducedBranch (d := d) OS lgc m ε ξ) * φ ξ) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        ∀ᵐ ξ : NPointDomain d m ∂volume,
          ‖(canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ -
              canonicalReducedBranch (d := d) OS lgc m ε ξ) * φ ξ‖ ≤ bound ξ)
    (hperm_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun ξ : NPointDomain d m =>
            canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * φ ξ)
          volume)
    (hcan_integrable :
      ∀ᶠ (ε : ℝ) in
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ),
        Integrable
          (fun ξ : NPointDomain d m =>
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ) volume) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * φ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) : Filter ℝ)
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
  let F : ℝ → NPointDomain d m → ℂ := fun ε ξ =>
    (canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ -
      canonicalReducedBranch (d := d) OS lgc m ε ξ) * φ ξ
  have hDCT :
      Filter.Tendsto
        (fun ε : ℝ => ∫ ξ : NPointDomain d m, F ε ξ)
        l (nhds (∫ ξ : NPointDomain d m, (0 : ℂ))) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      bound hF_meas hbound hbound_integrable
      (by
        refine Filter.Eventually.of_forall ?_
        intro ξ
        by_cases hφξ : φ ξ = 0
        · simp [F, hφξ]
        · simpa [F] using (hpointwise ξ hφξ).mul tendsto_const_nhds)
  have heq :
      (fun ε : ℝ =>
        (∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε ξ * φ ξ) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        =ᶠ[l]
      (fun ε : ℝ => ∫ ξ : NPointDomain d m, F ε ξ) := by
    filter_upwards [hperm_integrable, hcan_integrable] with ε hp hc
    rw [← MeasureTheory.integral_sub hp hc]
    congr 1
    ext ξ
    simp [F]
    ring
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa [l] using hDCT

/-- A local same-boundary packet gives the local two-branch comparison.

This is the reduced EOW payload shape: on one real neighborhood, both
positive-side branch pairings converge to the same distributional boundary
functional. -/
theorem reduced_local_comparison_of_sameBoundaryCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (V : Set (NPointDomain d m))
    (T : SchwartzNPoint d m →L[ℂ] ℂ)
    (hleft :
      ∀ ψ : SchwartzNPoint d m,
        HasCompactSupport (ψ : NPointDomain d m → ℂ) →
        tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ η : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                ψ η)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T ψ)))
    (hright :
      ∀ ψ : SchwartzNPoint d m,
        HasCompactSupport (ψ : NPointDomain d m → ℂ) →
        tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ η : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T ψ))) :
    ∀ ψ : SchwartzNPoint d m,
      HasCompactSupport (ψ : NPointDomain d m → ℂ) →
      tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              ψ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  intro ψ hψ_compact hψ_support
  have hsub :=
    (hleft ψ hψ_compact hψ_support).sub
      (hright ψ hψ_compact hψ_support)
  simpa using hsub

/-- Local reduced two-branch boundary comparisons assemble over a compact
reduced test support by a finite Schwartz partition of unity. -/
theorem reducedAfterSwap_tendsto_of_local_tsupport_cover
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hlocal :
      ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
        ∃ V : Set (NPointDomain d m),
          IsOpen V ∧ ξ ∈ V ∧
          ∀ ψ : SchwartzNPoint d m,
            HasCompactSupport (ψ : NPointDomain d m → ℂ) →
            tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
            Filter.Tendsto
              (fun ε : ℝ =>
                (∫ η : NPointDomain d m,
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                    ψ η) -
                ∫ η : NPointDomain d m,
                  canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ η : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
            φ η) -
        ∫ η : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  classical
  let K : Set (NPointDomain d m) := tsupport (φ : NPointDomain d m → ℂ)
  let β := {ξ : NPointDomain d m // ξ ∈ K}
  let Vβ : β → Set (NPointDomain d m) :=
    fun a => Classical.choose (hlocal a a.property)
  have hVβ_spec :
      ∀ a : β,
        IsOpen (Vβ a) ∧ (a : NPointDomain d m) ∈ Vβ a ∧
          ∀ ψ : SchwartzNPoint d m,
            HasCompactSupport (ψ : NPointDomain d m → ℂ) →
            tsupport (ψ : NPointDomain d m → ℂ) ⊆ Vβ a →
            Filter.Tendsto
              (fun ε : ℝ =>
                (∫ η : NPointDomain d m,
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                    ψ η) -
                ∫ η : NPointDomain d m,
                  canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds 0) := by
    intro a
    exact Classical.choose_spec (hlocal a a.property)
  have hK_cover : K ⊆ ⋃ a : β, Vβ a := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr ⟨⟨ξ, hξ⟩, (hVβ_spec ⟨ξ, hξ⟩).2.1⟩
  obtain ⟨t, htcover⟩ :=
    hφ_compact.isCompact.elim_finite_subcover Vβ
      (fun a => (hVβ_spec a).1) hK_cover
  let α := {a : β // a ∈ t}
  let Vα : α → Set (NPointDomain d m) := fun a => Vβ a.1
  have hVα_open : ∀ a : α, IsOpen (Vα a) := by
    intro a
    exact (hVβ_spec a.1).1
  have hcover :
      K ⊆ ⋃ a : α, Vα a := by
    intro ξ hξ
    rcases Set.mem_iUnion₂.mp (htcover (by simpa [K] using hξ)) with
      ⟨a, hat, hξa⟩
    exact Set.mem_iUnion.mpr ⟨⟨a, hat⟩, hξa⟩
  obtain ⟨χ, _hχ_compact, hχ_sub, hχ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := NPointDomain d m)
      (K := K)
      hφ_compact.isCompact
      hVα_open
      hcover
  let piece : α → SchwartzNPoint d m := fun a =>
    SchwartzMap.smulLeftCLM ℂ (χ a : NPointDomain d m → ℂ) φ
  have hpiece_compact :
      ∀ a, HasCompactSupport (piece a : NPointDomain d m → ℂ) := by
    intro a
    refine hφ_compact.mono' ?_
    intro ξ hξ
    have hξ_ts : ξ ∈ tsupport (piece a : NPointDomain d m → ℂ) :=
      subset_closure hξ
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ a : NPointDomain d m → ℂ))
        (f := φ)) hξ_ts).1
  have hpiece_support :
      ∀ a, tsupport (piece a : NPointDomain d m → ℂ) ⊆ Vα a := by
    intro a ξ hξ
    exact
      hχ_sub a
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (χ a : NPointDomain d m → ℂ))
          (f := φ)) hξ).2
  have hφ_sum : φ = ∑ a, piece a := by
    simpa [piece, K] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ φ
        (by
          intro ξ hξ
          simpa [K] using hχ_sum ξ hξ)
  have hpiece_tendsto :
      ∀ a,
        Filter.Tendsto
          (fun ε : ℝ =>
            (∫ η : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                piece a η) -
            ∫ η : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε η * piece a η)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
    intro a
    exact (hVβ_spec a.1).2.2 (piece a)
      (hpiece_compact a) (hpiece_support a)
  let diff : α → ℝ → ℂ := fun a ε =>
    (∫ η : NPointDomain d m,
      canonicalAfterReducedSwapBranch
          (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
        piece a η) -
    ∫ η : NPointDomain d m,
      canonicalReducedBranch (d := d) OS lgc m ε η * piece a η
  have hsum_tendsto :
      Filter.Tendsto
        (fun ε : ℝ => ∑ a, diff a ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [diff] using
      tendsto_finset_sum (s := Finset.univ)
        (fun a _ha => hpiece_tendsto a)
  refine Filter.Tendsto.congr' ?_ hsum_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := Set.mem_Ioi.mp hε
  let A : NPointDomain d m → ℂ := fun η =>
    canonicalAfterReducedSwapBranch
      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η
  let C : NPointDomain d m → ℂ := fun η =>
    canonicalReducedBranch (d := d) OS lgc m ε η
  have hIntA :
      ∀ a ∈ (Finset.univ : Finset α),
        Integrable (fun η : NPointDomain d m => A η * piece a η) := by
    intro a _ha
    simpa [A] using
      canonicalAfterReducedSwapBranch_integrable_of_pos
        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε hεpos
        (piece a) (hpiece_compact a)
  have hIntC :
      ∀ a ∈ (Finset.univ : Finset α),
        Integrable (fun η : NPointDomain d m => C η * piece a η) := by
    intro a _ha
    simpa [C] using
      canonicalReducedBranch_integrable_of_pos
        (d := d) OS lgc m ε hεpos (piece a) (hpiece_compact a)
  simp only [diff]
  rw [hφ_sum]
  change
    (∑ a,
        ((∫ η : NPointDomain d m, A η * piece a η) -
          ∫ η : NPointDomain d m, C η * piece a η)) =
      (∫ η : NPointDomain d m,
          A η * ((∑ a, piece a : SchwartzNPoint d m) η)) -
        ∫ η : NPointDomain d m,
          C η * ((∑ a, piece a : SchwartzNPoint d m) η)
  have hmulA :
      (fun η : NPointDomain d m =>
          A η * ((∑ a, piece a : SchwartzNPoint d m) η)) =
        fun η : NPointDomain d m => ∑ a, A η * piece a η := by
    funext η
    simp [Finset.mul_sum]
  have hmulC :
      (fun η : NPointDomain d m =>
          C η * ((∑ a, piece a : SchwartzNPoint d m) η)) =
        fun η : NPointDomain d m => ∑ a, C η * piece a η := by
    funext η
    simp [Finset.mul_sum]
  rw [hmulA, hmulC]
  rw [integral_finset_sum (s := Finset.univ) hIntA,
    integral_finset_sum (s := Finset.univ) hIntC]
  simp [Finset.sum_sub_distrib]

/-- Local same-boundary reduced EOW packets assemble over a compact reduced
test support. -/
theorem reducedAfterSwap_tendsto_of_local_sameBoundaryCLM_cover
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m)
    (hφ_compact : HasCompactSupport (φ : NPointDomain d m → ℂ))
    (hlocal :
      ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
        ∃ (V : Set (NPointDomain d m))
          (T : SchwartzNPoint d m →L[ℂ] ℂ),
          IsOpen V ∧ ξ ∈ V ∧
          (∀ ψ : SchwartzNPoint d m,
            HasCompactSupport (ψ : NPointDomain d m → ℂ) →
            tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ η : NPointDomain d m,
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                    ψ η)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (T ψ))) ∧
          (∀ ψ : SchwartzNPoint d m,
            HasCompactSupport (ψ : NPointDomain d m → ℂ) →
            tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ η : NPointDomain d m,
                  canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (T ψ)))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ η : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
            φ η) -
        ∫ η : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  refine
    reducedAfterSwap_tendsto_of_local_tsupport_cover
      (d := d) OS lgc m i hi φ hφ_compact ?_
  intro ξ hξ
  rcases hlocal ξ hξ with
    ⟨V, T, hV_open, hξV, hleft, hright⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  exact
    reduced_local_comparison_of_sameBoundaryCLM
      (d := d) OS lgc m i hi V T hleft hright

/-- A local comparison with separate normalized basepoint cutoffs on the two
boundary CLMs still gives the local branch-difference limit.

This is the local moving-cutoff version needed by the Jost/Ruelle packet:
after cutoff independence, the two boundary functionals can be compared as one
CLM without assuming the local construction made identical cutoff choices. -/
theorem reduced_local_comparison_of_cutoffBoundaryCLMs
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χL χR : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (V : Set (NPointDomain d m))
    (hleft :
      ∀ ψ : SchwartzNPoint d m,
        HasCompactSupport (ψ : NPointDomain d m → ℂ) →
        tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ η : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                ψ η)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χL m ψ)))
    (hright :
      ∀ ψ : SchwartzNPoint d m,
        HasCompactSupport (ψ : NPointDomain d m → ℂ) →
        tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ η : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χR m ψ))) :
    ∀ ψ : SchwartzNPoint d m,
      HasCompactSupport (ψ : NPointDomain d m → ℂ) →
      tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              ψ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  refine
    reduced_local_comparison_of_sameBoundaryCLM
      (d := d) OS lgc m i hi V
      (bvt_reducedWightmanCLM (d := d) OS lgc χR m) ?_ hright
  intro ψ hψ_compact hψ_support
  have hcut :
      bvt_reducedWightmanCLM (d := d) OS lgc χL m ψ =
        bvt_reducedWightmanCLM (d := d) OS lgc χR m ψ := by
    exact congrArg
      (fun T : SchwartzNPoint d m →L[ℂ] ℂ => T ψ)
      (bvt_reducedWightmanCLM_eq_of_cutoff
        (d := d) OS lgc m χL χR)
  simpa [hcut] using hleft ψ hψ_compact hψ_support

/-- Pointwise local branch-difference packets imply the global reduced
canonical adjacent-swap boundary invariant.

This is the direct consumer for a Jost/Ruelle theorem stated as local
distributional vanishing of the adjacent-after-swap branch minus the canonical
branch. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_branchDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  (∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η) -
                  ∫ η : NPointDomain d m,
                    canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds 0)) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_support
  have hbranch :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              φ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    reducedAfterSwap_tendsto_of_local_tsupport_cover
      (d := d) OS lgc m i hi φ hφ_compact
      (hlocal m i hi φ hφ_compact hφ_support)
  refine Filter.Tendsto.congr' ?_ hbranch
  filter_upwards with ε
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]

/-- Local eventual branch equality on support collars implies the global
reduced canonical adjacent-swap boundary invariant.

This is the direct smearing handoff for the Jost/Ruelle mixed-tube step: once
the two local holomorphic branches have been identified on a neighborhood of
each support point, the already checked finite Schwartz partition-of-unity
consumer turns that local branch equality into the reduced theorem-2 boundary
invariant. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_eventual_branch_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
                ∀ η ∈ tsupport (ψ : NPointDomain d m → ℂ),
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η =
                    canonicalReducedBranch (d := d) OS lgc m ε η) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  refine
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_branchDifference
      (d := d) OS lgc ?_
  intro m i hi φ hφ_compact hφ_support ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_support ξ hξ with
    ⟨V, hV_open, hξV, hV_eq⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_support
  have heq_branch := hV_eq ψ hψ_compact hψ_support
  have heq_integrals :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (∫ η : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
            ψ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η =
        0 := by
    filter_upwards [heq_branch] with ε hε
    have hfun :
        (fun η : NPointDomain d m =>
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
            ψ η) =
        (fun η : NPointDomain d m =>
          canonicalReducedBranch (d := d) OS lgc m ε η * ψ η) := by
      funext η
      by_cases hη : η ∈ tsupport (ψ : NPointDomain d m → ℂ)
      · rw [hε η hη]
      · have hψ_zero : ψ η = 0 := image_eq_zero_of_notMem_tsupport hη
        simp [hψ_zero]
    rw [hfun, sub_self]
  have heq_eventually :
      (fun _ : ℝ => (0 : ℂ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              ψ η) -
            ∫ η : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε η * ψ η := by
    filter_upwards [heq_integrals] with ε hε
    exact hε.symm
  exact Tendsto.congr' heq_eventually tendsto_const_nhds

/-- Local eventual branch equality on closed-support collars implies the
closed-support reduced canonical adjacent-swap boundary invariant.

This is the production version of the book-faithful support handoff: the finite
cover is taken over `tsupport φ`, and every localized test is required to have
topological support in the collar on which the mixed-tube branches agree. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_eventual_branch_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
                ∀ η ∈ tsupport (ψ : NPointDomain d m → ℂ),
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η =
                    canonicalReducedBranch (d := d) OS lgc m ε η) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_tsupport
  have hbranch :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              φ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    refine
      reducedAfterSwap_tendsto_of_local_tsupport_cover
        (d := d) OS lgc m i hi φ hφ_compact ?_
    intro ξ hξ
    rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
      ⟨V, hV_open, hξV, hV_eq⟩
    refine ⟨V, hV_open, hξV, ?_⟩
    intro ψ hψ_compact hψ_support
    have heq_branch := hV_eq ψ hψ_compact hψ_support
    have heq_integrals :
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              ψ η) -
            ∫ η : NPointDomain d m,
              canonicalReducedBranch (d := d) OS lgc m ε η * ψ η =
          0 := by
      filter_upwards [heq_branch] with ε hε
      have hfun :
          (fun η : NPointDomain d m =>
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              ψ η) =
          (fun η : NPointDomain d m =>
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η) := by
        funext η
        by_cases hη : η ∈ tsupport (ψ : NPointDomain d m → ℂ)
        · rw [hε η hη]
        · have hψ_zero : ψ η = 0 := image_eq_zero_of_notMem_tsupport hη
          simp [hψ_zero]
      rw [hfun, sub_self]
    have heq_eventually :
        (fun _ : ℝ => (0 : ℂ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun ε : ℝ =>
            (∫ η : NPointDomain d m,
              canonicalAfterReducedSwapBranch
                  (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                ψ η) -
              ∫ η : NPointDomain d m,
                canonicalReducedBranch (d := d) OS lgc m ε η * ψ η := by
      filter_upwards [heq_integrals] with ε hε
      exact hε.symm
    exact Tendsto.congr' heq_eventually tendsto_const_nhds
  refine Filter.Tendsto.congr' ?_ hbranch
  filter_upwards with ε
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]

/-- Local distributional branch-difference packets imply the closed-support
reduced canonical adjacent-swap boundary invariant.

This is the closed-support partition-of-unity handoff in the form produced by
the OS-I `(4.14)` source-side argument: on each reduced spacelike collar, the
two boundary approach integrals only have to have vanishing difference. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_branchDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  (∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η) -
                  ∫ η : NPointDomain d m,
                    canonicalReducedBranch (d := d) OS lgc m ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds 0)) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_tsupport
  have hbranch :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              φ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    refine
      reducedAfterSwap_tendsto_of_local_tsupport_cover
        (d := d) OS lgc m i hi φ hφ_compact ?_
    intro ξ hξ
    rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
      ⟨V, hV_open, hξV, hVdiff⟩
    exact ⟨V, hV_open, hξV, hVdiff⟩
  refine Filter.Tendsto.congr' ?_ hbranch
  filter_upwards with ε
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]

/-- Pointwise local same-boundary packets imply the closed-support reduced
canonical adjacent-swap boundary invariant.

This is the closed-support version of the boundary-CLM handoff used by the
book proof: the local mixed-tube construction may produce a common boundary
functional on each support collar, and the finite-cover theorem smears those
local boundary values. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_sameBoundaryCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ (V : Set (NPointDomain d m))
            (T : SchwartzNPoint d m →L[ℂ] ℂ),
            IsOpen V ∧ ξ ∈ V ∧
            (∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (T ψ))) ∧
            (∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalReducedBranch (d := d) OS lgc m ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (T ψ)))) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_tsupport
  have hbranch :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              φ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    reducedAfterSwap_tendsto_of_local_sameBoundaryCLM_cover
      (d := d) OS lgc m i hi φ hφ_compact
      (hlocal m i hi φ hφ_compact hφ_tsupport)
  refine Filter.Tendsto.congr' ?_ hbranch
  filter_upwards with ε
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]

/-- Local adjacent-after-swap boundary packets imply the closed-support reduced
canonical adjacent-swap boundary invariant.

The canonical reduced branch side is supplied by the existing reduced Wightman
boundary CLM theorem; the local analytic input only has to prove that the
adjacent-after-swap branch has that same boundary CLM on each support collar. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_adjacentBoundaryCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (bvt_reducedWightmanCLM
                  (d := d) OS lgc χ m ψ))) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  refine
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_sameBoundaryCLM
      (d := d) OS lgc ?_
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hleft⟩
  refine
    ⟨V, bvt_reducedWightmanCLM (d := d) OS lgc χ m,
      hV_open, hξV, hleft, ?_⟩
  intro ψ _hψ_compact _hψ_support
  exact
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m ψ

/-- Local reduced boundary-CLM invariance, in the form supplied by the
mixed-tube/Jost/Ruelle boundary-value theorem.

The statement is deliberately one level below theorem-2 locality: it only says
that the descended reduced Wightman CLM is invariant under the induced adjacent
real transposition on small collars of the closed reduced spacelike support. -/
def ReducedLocalAdjacentBoundaryCLMInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d) : Prop :=
  ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m),
    HasCompactSupport (φ : NPointDomain d m → ℂ) →
    tsupport (φ : NPointDomain d m → ℂ) ⊆
      reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
    ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
      ∃ V : Set (NPointDomain d m),
        IsOpen V ∧ ξ ∈ V ∧
        ∀ ψ : SchwartzNPoint d m,
          HasCompactSupport (ψ : NPointDomain d m → ℂ) →
          tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
          bvt_reducedWightmanCLM (d := d) OS lgc χ m
              (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (realPermOnReducedDiffCLE (d := d) m
                  (Equiv.swap i ⟨i.val + 1, hi⟩)) ψ) =
            bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ

/-- The local distributional branch-difference theorem is exactly strong enough
to supply the monograph-facing local reduced boundary-CLM invariant.

This is the local endpoint-uniqueness step: the adjacent-after-swap branch has
boundary value `bvt_reducedWightmanCLM` after the induced adjacent real
permutation, the canonical branch has boundary value
`bvt_reducedWightmanCLM`, and the local branch-difference limit forces those
two CLM values to agree on every support collar. -/
theorem reducedLocalAdjacentBoundaryCLMInvariant_of_local_branchDifference
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        tsupport (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  (∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η) -
                  ∫ η : NPointDomain d m,
                    canonicalReducedBranch (d := d) OS lgc m ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds 0)) :
    ReducedLocalAdjacentBoundaryCLMInvariant (d := d) OS lgc χ := by
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hVdiff⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let ψτ : SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m (Equiv.swap i j)) ψ
  have hafter :
      Tendsto
        (fun ε : ℝ =>
          ∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε η *
              ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m ψτ)) := by
    simpa [j, ψτ] using
      canonicalAfterReducedSwapBranch_tendsto_bvt_reducedWightmanCLM_comp
        (d := d) OS lgc χ m i hi ψ
  have hcanon :
      Tendsto
        (fun ε : ℝ =>
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m ψ
  have hdiff_limit :
      Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε η *
              ψ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_reducedWightmanCLM (d := d) OS lgc χ m ψτ -
            bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ)) := by
    exact hafter.sub hcanon
  have hlocal_limit :
      Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch (d := d) OS lgc m i j ε η *
              ψ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [j] using hVdiff ψ hψ_compact hψ_tsupport
  have hzero :
      bvt_reducedWightmanCLM (d := d) OS lgc χ m ψτ -
          bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ =
        0 :=
    tendsto_nhds_unique hdiff_limit hlocal_limit
  simpa [ψτ, j] using sub_eq_zero.mp hzero

/-- The local reduced CLM invariant supplies the local adjacent-boundary CLM
packet used by the closed-support reduced Ruelle handoff. -/
theorem local_adjacentBoundaryCLM_of_reducedLocalAdjacentBoundaryCLMInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocalCLM :
      ReducedLocalAdjacentBoundaryCLMInvariant (d := d) OS lgc χ) :
    ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
      (φ : SchwartzNPoint d m),
      HasCompactSupport (φ : NPointDomain d m → ℂ) →
      tsupport (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
      ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
        ∃ V : Set (NPointDomain d m),
          IsOpen V ∧ ξ ∈ V ∧
          ∀ ψ : SchwartzNPoint d m,
            HasCompactSupport (ψ : NPointDomain d m → ℂ) →
            tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ η : NPointDomain d m,
                  canonicalAfterReducedSwapBranch
                      (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                    ψ η)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (bvt_reducedWightmanCLM
                (d := d) OS lgc χ m ψ)) := by
  intro m i hi φ hφ_compact hφ_tsupport ξ hξ
  rcases hlocalCLM m i hi φ hφ_compact hφ_tsupport ξ hξ with
    ⟨V, hV_open, hξV, hV_clm⟩
  refine ⟨V, hV_open, hξV, ?_⟩
  intro ψ hψ_compact hψ_tsupport
  have hboundary :=
    canonicalAfterReducedSwapBranch_tendsto_bvt_reducedWightmanCLM_comp
      (d := d) OS lgc χ m i hi ψ
  have hclm := hV_clm ψ hψ_compact hψ_tsupport
  simpa [hclm] using hboundary

/-- The monograph-facing local reduced CLM invariant is sufficient for the
closed-support reduced canonical adjacent-swap invariant. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_reducedBoundaryCLMInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocalCLM :
      ReducedLocalAdjacentBoundaryCLMInvariant (d := d) OS lgc χ) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  exact
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_local_adjacentBoundaryCLM
      (d := d) OS lgc χ
      (local_adjacentBoundaryCLM_of_reducedLocalAdjacentBoundaryCLMInvariant
        (d := d) OS lgc χ hlocalCLM)

/-- Closed-support reduced canonical adjacent-swap invariance gives the
corresponding reduced boundary-CLM equality on the same closed-support tests.

This is the boundary-value last mile in the Jost/Ruelle locality route: both
canonical integrals have the `bvt_reducedWightmanCLM` boundary value, and the
closed-support branch-difference limit forces those two boundary values to
coincide. -/
theorem reducedBoundaryCLM_invariant_of_closedSupportCanonicalInvariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hclosed :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
        (d := d) OS lgc) :
    ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
      (φ : SchwartzNPoint d m),
      HasCompactSupport (φ : NPointDomain d m → ℂ) →
      tsupport (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
      bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
        bvt_reducedWightmanCLM (d := d) OS lgc χ m φ := by
  intro m i hi φ hφ_compact hφ_tsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let φτ : SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m τ) φ
  have hτ :
      Tendsto
        (fun ε : ℝ =>
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m φτ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m φτ
  have hφ :
      Tendsto
        (fun ε : ℝ =>
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m φ
  have hdiff_limit :
      Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_reducedWightmanCLM (d := d) OS lgc χ m φτ -
            bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)) := by
    exact hτ.sub hφ
  have hclosed_limit :
      Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    refine Tendsto.congr' ?_ (hclosed m i hi φ hφ_compact hφ_tsupport)
    filter_upwards with ε
    congr 1
  have hzero :
      bvt_reducedWightmanCLM (d := d) OS lgc χ m φτ -
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ =
        0 :=
    tendsto_nhds_unique hdiff_limit hclosed_limit
  simpa [φτ, τ, j] using sub_eq_zero.mp hzero

/-- Pointwise local same-boundary packets imply the global reduced canonical
adjacent-swap boundary invariant. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_sameBoundaryCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ (V : Set (NPointDomain d m))
            (T : SchwartzNPoint d m →L[ℂ] ℂ),
            IsOpen V ∧ ξ ∈ V ∧
            (∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (T ψ))) ∧
            (∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalReducedBranch (d := d) OS lgc m ε η * ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (T ψ)))) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_support
  have hbranch :
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ η : NPointDomain d m,
            canonicalAfterReducedSwapBranch
                (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
              φ η) -
          ∫ η : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε η * φ η)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) :=
    reducedAfterSwap_tendsto_of_local_sameBoundaryCLM_cover
      (d := d) OS lgc m i hi φ hφ_compact
      (hlocal m i hi φ hφ_compact hφ_support)
  refine Filter.Tendsto.congr' ?_ hbranch
  filter_upwards with ε
  rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
    (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]

/-- Pointwise local adjacent-after-swap boundary packets imply the global
reduced canonical adjacent-swap boundary invariant.

The canonical branch side is supplied by
`canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM`; the remaining local
analytic input is only that the adjacent-after-swap branch has this same
boundary CLM. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_adjacentBoundaryCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hlocal :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        ∀ ξ ∈ tsupport (φ : NPointDomain d m → ℂ),
          ∃ V : Set (NPointDomain d m),
            IsOpen V ∧ ξ ∈ V ∧
            ∀ ψ : SchwartzNPoint d m,
              HasCompactSupport (ψ : NPointDomain d m → ℂ) →
              tsupport (ψ : NPointDomain d m → ℂ) ⊆ V →
              Filter.Tendsto
                (fun ε : ℝ =>
                  ∫ η : NPointDomain d m,
                    canonicalAfterReducedSwapBranch
                        (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε η *
                      ψ η)
                (nhdsWithin 0 (Set.Ioi 0))
                (nhds (bvt_reducedWightmanCLM
                  (d := d) OS lgc χ m ψ))) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  refine
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_local_sameBoundaryCLM
      (d := d) OS lgc ?_
  intro m i hi φ hφ_compact hφ_support ξ hξ
  rcases hlocal m i hi φ hφ_compact hφ_support ξ hξ with
    ⟨V, hV_open, hξV, hleft⟩
  refine
    ⟨V, bvt_reducedWightmanCLM (d := d) OS lgc χ m,
      hV_open, hξV, hleft, ?_⟩
  intro ψ _hψ_compact _hψ_support
  exact
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m ψ

/-- Reduced boundary-CLM invariance is exactly strong enough for the compact
Schwartz-test adjacent-swap invariant.

This is the remaining local Jost/Ruelle conclusion in CLM form: on compact
tests supported in the selected adjacent spacelike reduced edge, the descended
Wightman boundary functional is unchanged by the induced adjacent real swap. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_boundaryCLM_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hinv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χ m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χ m φ) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let φτ : SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m τ) φ
  have hτ :
      Tendsto
        (fun ε : ℝ =>
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m φτ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m φτ
  have hφ :
      Tendsto
        (fun ε : ℝ =>
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m φ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m φ
  have hlim :
      bvt_reducedWightmanFamily (d := d) OS lgc χ m φτ -
          bvt_reducedWightmanFamily (d := d) OS lgc χ m φ =
        0 := by
    have h :=
      hinv m i hi φ hφ_compact (by simpa [j] using hφ_support)
    simpa [bvt_reducedWightmanCLM_apply, φτ, τ, j] using sub_eq_zero.mpr h
  have hdiff :
      Tendsto
        (fun ε : ℝ =>
          (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ) -
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [hlim] using hτ.sub hφ
  refine Tendsto.congr' ?_ hdiff
  filter_upwards with ε
  congr 1

/-- Reduced boundary-CLM invariance with separate left/right normalized
cutoffs still gives the compact Schwartz-test adjacent-swap invariant.

This is the handoff shape needed when a local Jost/Ruelle construction
produces the two boundary CLMs using different basepoint cutoffs.  The
non-circular cutoff-independence theorem in
`OSToWightmanReducedCanonicalBoundaryCLM` reduces it to the fixed-cutoff
consumer above. -/
theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_boundaryCLM_invariant_two_cutoffs
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χL χR : BHW.NormalizedBasepointCutoff d)
    (hinv :
      ∀ (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
        (φ : SchwartzNPoint d m),
        HasCompactSupport (φ : NPointDomain d m → ℂ) →
        Function.support (φ : NPointDomain d m → ℂ) ⊆
          reducedSpacelikeSwapEdge (d := d) m i ⟨i.val + 1, hi⟩ →
        bvt_reducedWightmanCLM (d := d) OS lgc χL m
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realPermOnReducedDiffCLE (d := d) m
                (Equiv.swap i ⟨i.val + 1, hi⟩)) φ) =
          bvt_reducedWightmanCLM (d := d) OS lgc χR m φ) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  refine
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_boundaryCLM_invariant
      (d := d) OS lgc χR ?_
  intro m i hi φ hφ_compact hφ_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j
  let φτ : SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m τ) φ
  have hcut :
      bvt_reducedWightmanCLM (d := d) OS lgc χR m φτ =
        bvt_reducedWightmanCLM (d := d) OS lgc χL m φτ := by
    exact congrArg
      (fun T : SchwartzNPoint d m →L[ℂ] ℂ => T φτ)
      (bvt_reducedWightmanCLM_eq_of_cutoff
        (d := d) OS lgc m χR χL)
  calc
    bvt_reducedWightmanCLM (d := d) OS lgc χR m φτ
        = bvt_reducedWightmanCLM (d := d) OS lgc χL m φτ := hcut
    _ = bvt_reducedWightmanCLM (d := d) OS lgc χR m φ := by
          simpa [φτ, τ, j] using
            hinv m i hi φ hφ_compact hφ_support

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_fiberMarginal_withCutoff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hχ_compact :
      HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hRuelle : AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_support
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz φ
  have hf_compact :
      HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) := by
    simpa [f] using
      reducedTestLift_hasCompactSupport
        (d := d) χ.toSchwartz φ hχ_compact hφ_compact
  have hf_support :
      ∀ x, f.toFun x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [f, j] using
      reducedTestLift_reduced_support_subset
        (d := d) i hi χ.toSchwartz φ hφ_support
  have hruelle :
      Filter.Tendsto
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
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [f, j] using hRuelle m i hi f hf_compact hf_support
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
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ) := by
    filter_upwards with ε
    have hdiff :=
      adjacentReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
        (d := d) OS lgc m i hi f ε
    have hmargin :
        reducedFiberMarginal (d := d) m f =
          (φ : NPointDomain d m → ℂ) := by
      simpa [f] using
        reducedFiberMarginal_reducedTestLift_eq
          (d := d) m χ φ
    have hfirst_raw :
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ) := by
      simpa [adjacentReducedFiberDifference, reducedFiberBranchDifference,
        adjacentReducedPermutedBranch, canonicalReducedBranch,
        reducedFiberMarginal, j]
        using hdiff
    have hfirst_rhs :
        (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ)) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              (φ : NPointDomain d m → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ
      have hpoint :
          reducedFiberIntegral (d := d) m
              (f : NPointDomain d (m + 1) → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i j) ξ) =
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i j) ξ) := by
        simpa [reducedFiberMarginal] using
          congrFun hmargin
            (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ)
      rw [hpoint]
    have hfirst := hfirst_raw.trans hfirst_rhs
    have hsecond :
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ
      have hpoint :
          reducedFiberIntegral (d := d) m
              (f : NPointDomain d (m + 1) → ℂ) ξ =
            (φ : NPointDomain d m → ℂ) ξ := by
        simpa [reducedFiberMarginal] using congrFun hmargin ξ
      rw [hpoint]
      rfl
    rw [hfirst, hsecond]
  exact Filter.Tendsto.congr' htransport hruelle

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_fiberMarginal_withCutoff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (hχ_compact :
      HasCompactSupport (χ.toSchwartz : SpacetimeDim d → ℂ))
    (hRuelle : AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  intro m i hi φ hφ_compact hφ_tsupport
  let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
  have hφ_support :
      Function.support (φ : NPointDomain d m → ℂ) ⊆
        reducedSpacelikeSwapEdge (d := d) m i j := by
    intro ξ hξ
    exact hφ_tsupport (subset_tsupport _ hξ)
  let f : SchwartzNPoint d (m + 1) :=
    BHW.reducedTestLift m d χ.toSchwartz φ
  have hf_compact :
      HasCompactSupport (f : NPointDomain d (m + 1) → ℂ) := by
    simpa [f] using
      reducedTestLift_hasCompactSupport
        (d := d) χ.toSchwartz φ hχ_compact hφ_compact
  have hf_support :
      ∀ x, f.toFun x ≠ 0 →
        BHW.reducedDiffMapReal (m + 1) d x ∈
          reducedSpacelikeSwapEdge (d := d) m i j := by
    simpa [f, j] using
      reducedTestLift_reduced_support_subset
        (d := d) i hi χ.toSchwartz φ hφ_support
  have hruelle :
      Filter.Tendsto
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
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [f, j] using hRuelle m i hi f hf_compact hf_support
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
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ)) -
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ) := by
    filter_upwards with ε
    have hdiff :=
      adjacentReducedFiberDifference_adjacent_eq_canonicalReducedBranch_comp_sub
        (d := d) OS lgc m i hi f ε
    have hmargin :
        reducedFiberMarginal (d := d) m f =
          (φ : NPointDomain d m → ℂ) := by
      simpa [f] using
        reducedFiberMarginal_reducedTestLift_eq
          (d := d) m χ φ
    have hfirst_raw :
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε *
                    permutedCanonicalReducedDirectionC
                      (d := d) m (Equiv.swap i j) k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ) := by
      simpa [adjacentReducedFiberDifference, reducedFiberBranchDifference,
        adjacentReducedPermutedBranch, canonicalReducedBranch,
        reducedFiberMarginal, j]
        using hdiff
    have hfirst_rhs :
        (∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ)) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ *
              (φ : NPointDomain d m → ℂ)
                (realPermOnReducedDiff (d := d) m
                  (Equiv.swap i j) ξ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ
      have hpoint :
          reducedFiberIntegral (d := d) m
              (f : NPointDomain d (m + 1) → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i j) ξ) =
            (φ : NPointDomain d m → ℂ)
              (realPermOnReducedDiff (d := d) m
                (Equiv.swap i j) ξ) := by
        simpa [reducedFiberMarginal] using
          congrFun hmargin
            (realPermOnReducedDiff (d := d) m (Equiv.swap i j) ξ)
      rw [hpoint]
    have hfirst := hfirst_raw.trans hfirst_rhs
    have hsecond :
        (∫ ξ : NPointDomain d m,
            bvt_F_reduced (d := d) OS lgc m
              (fun k μ =>
                (ξ k μ : ℂ) +
                  ε * canonicalReducedDirectionC (d := d) m k μ *
                    Complex.I) *
              reducedFiberIntegral (d := d) m
                (f : NPointDomain d (m + 1) → ℂ) ξ) =
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φ ξ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ξ
      have hpoint :
          reducedFiberIntegral (d := d) m
              (f : NPointDomain d (m + 1) → ℂ) ξ =
            (φ : NPointDomain d m → ℂ) ξ := by
        simpa [reducedFiberMarginal] using congrFun hmargin ξ
      rw [hpoint]
      rfl
    rw [hfirst, hsecond]
  exact Filter.Tendsto.congr' htransport hruelle

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_fiberMarginal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hRuelle : AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc := by
  exact
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartz_of_fiberMarginal_withCutoff
      (d := d) OS lgc (BHW.normalizedCutoffOfBump d)
      (BHW.normalizedCutoffOfBump_hasCompactSupport d) hRuelle

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_fiberMarginal
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hRuelle : AdjacentReducedRuelleFiberMarginalLimit (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  exact
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_fiberMarginal_withCutoff
      (d := d) OS lgc (BHW.normalizedCutoffOfBump d)
      (BHW.normalizedCutoffOfBump_hasCompactSupport d) hRuelle

theorem reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_distributional
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hRuelle : AdjacentReducedRuelleDistributionalLimit (d := d) OS lgc) :
    ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport
      (d := d) OS lgc := by
  exact
    reducedCanonicalAdjacentSwapBoundaryInvariantSchwartzClosedSupport_of_fiberMarginal
      (d := d) OS lgc
      (adjacentReducedRuelleFiberMarginalLimit_of_distributional
        (d := d) OS lgc hRuelle)

/-- The book-faithful Schwartz-test reduced canonical invariant closes the
adjacent Wightman locality consumer used by theorem 2. -/
theorem bvt_W_swap_pairing_of_spacelike_from_canonicalBoundaryInvariantSchwartz
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hcanon :
      ReducedCanonicalAdjacentSwapBoundaryInvariantSchwartz (d := d) OS lgc) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d
          (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x =
        f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      bvt_W OS lgc n f = bvt_W OS lgc n g := by
  exact
    bvt_W_swap_pairing_of_spacelike_from_adjacent_reduced_ruelle_distributional
      (d := d) OS lgc
      (adjacentReducedRuelleDistributionalLimit_of_fiberMarginal
        (d := d) OS lgc
        (adjacentReducedRuelleFiberMarginalLimit_of_canonicalBoundaryInvariantSchwartz
          (d := d) OS lgc hcanon))

end OSReconstruction
