/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFrequencyReduction
import Init
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.EdgeDistribution
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport
import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.SCV.LocalContinuousEOW
import OSReconstruction.SCV.DistributionalEOWSupport
import Mathlib.Topology.MetricSpace.Thickening
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalEOWChartEnvelope
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.LocalProductRecovery
import OSReconstruction.Wightman.SpectralEquivalence









open MeasureTheory Filter

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

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
      change y (σ 0) μ = x₀ μ + c μ
      exact h
    have hz_base : z 0 = x₀ + c := by
      ext μ
      have h :=
        congrFun
          (congrFun
            (realDiffCoordCLE_symm_prependBasepointReal_eq_diffVarSection
              (d := d) m (x₀ + c) η)
            0)
          μ
      change z 0 μ = (x₀ + c) μ + diffVarSection d m η 0 μ at h
      simpa only [diffVarSection_zero, add_zero] using h
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
        change y (σ j.succ) μ - y (σ j.castSucc) μ = η j μ at hleft
        change z j.succ μ - z j.castSucc μ = η j μ at hright
        exact hleft.trans hright.symm
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
        exact continuous_pi fun μ =>
          (continuous_apply μ).comp ((continuous_apply i).comp continuous_snd)
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
/-- Topological support of a reduced test lift lies over the topological support
of the reduced test under the reduced-difference projection. -/
theorem reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
    {m : ℕ}
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m) :
    tsupport
        ((BHW.reducedTestLift m d χ φ : SchwartzNPoint d (m + 1)) :
          NPointDomain d (m + 1) → ℂ) ⊆
      (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
        tsupport (φ : NPointDomain d m → ℂ) := by
  let f : NPointDomain d (m + 1) → ℂ :=
    ((BHW.reducedTestLift m d χ φ : SchwartzNPoint d (m + 1)) :
      NPointDomain d (m + 1) → ℂ)
  have hsupport :
      Function.support f ⊆
        (BHW.reducedDiffMapRealCLM (m + 1) d) ⁻¹'
          tsupport (φ : NPointDomain d m → ℂ) := by
    intro x hx
    have hφ_ne :
        (φ : NPointDomain d m → ℂ)
            (BHW.reducedDiffMapReal (m + 1) d x) ≠ 0 := by
      intro hzero
      apply hx
      change BHW.reducedTestLift m d χ φ x = 0
      rw [BHW.reducedTestLift_apply, mul_eq_zero]
      exact Or.inr hzero
    simpa [BHW.reducedDiffMapRealCLM] using
      subset_tsupport (φ : NPointDomain d m → ℂ) hφ_ne
  exact
    closure_minimal hsupport
      ((isClosed_tsupport (φ : NPointDomain d m → ℂ)).preimage
        (BHW.reducedDiffMapRealCLM (m + 1) d).continuous)

end OSReconstruction
