import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSelectedReducedInput
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport

/-!
# Canonical Reduced Boundary CLM

This file packages the easy half of the reduced local same-boundary packet on
the theorem-2 E-to-R route.  The canonical reduced branch already has its
distributional boundary value by the selected reduced boundary-value theorem;
the remaining Jost/Ruelle work is to prove that the adjacent-after-swap branch
has this same local boundary value.
-/

open MeasureTheory Filter

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The descended reduced Wightman boundary functional as a continuous linear
map in the reduced Schwartz test. -/
noncomputable def bvt_reducedWightmanCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) :
    SchwartzNPoint d m →L[ℂ] ℂ := by
  refine
    { toLinearMap :=
        { toFun := fun ψ =>
            bvt_W OS lgc (m + 1)
              (BHW.reducedTestLift m d χ.toSchwartz ψ)
          map_add' := ?_
          map_smul' := ?_ }
      cont := ?_ }
  · intro ψ₁ ψ₂
    change
      bvt_W OS lgc (m + 1)
          (BHW.reducedTestLift m d χ.toSchwartz (ψ₁ + ψ₂)) =
        bvt_W OS lgc (m + 1)
            (BHW.reducedTestLift m d χ.toSchwartz ψ₁) +
          bvt_W OS lgc (m + 1)
            (BHW.reducedTestLift m d χ.toSchwartz ψ₂)
    rw [(BHW.reducedTestLift m d χ.toSchwartz).map_add]
    exact (bvt_W_linear (d := d) OS lgc (m + 1)).map_add _ _
  · intro c ψ
    change
      bvt_W OS lgc (m + 1)
          (BHW.reducedTestLift m d χ.toSchwartz (c • ψ)) =
        c *
          bvt_W OS lgc (m + 1)
            (BHW.reducedTestLift m d χ.toSchwartz ψ)
    rw [(BHW.reducedTestLift m d χ.toSchwartz).map_smul]
    simpa [smul_eq_mul] using
      (bvt_W_linear (d := d) OS lgc (m + 1)).map_smul c
        (BHW.reducedTestLift m d χ.toSchwartz ψ)
  · exact
      (bvt_W_continuous (d := d) OS lgc (m + 1)).comp
        (BHW.reducedTestLift m d χ.toSchwartz).continuous

@[simp] theorem bvt_reducedWightmanCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (ψ : SchwartzNPoint d m) :
    bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ =
      bvt_reducedWightmanFamily (d := d) OS lgc χ m ψ := by
  rfl

/-- For fixed reduced test, the `χ`-slot reduced `bvt_W` pairing as a CLM.

This is the non-circular cutoff-independence substrate: it uses only the
checked continuity/linearity of `bvt_W`, not locality or cluster. -/
noncomputable def bvt_reducedWightmanCutoffCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (φ : SchwartzNPoint d m) :
    SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ := by
  refine
    { toLinearMap :=
        { toFun := fun χ =>
            bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ φ)
          map_add' := ?_
          map_smul' := ?_ }
      cont := ?_ }
  · intro χ₁ χ₂
    change
      bvt_W OS lgc (m + 1)
          (BHW.reducedTestLiftCLMLeft m d φ (χ₁ + χ₂)) =
        bvt_W OS lgc (m + 1)
            (BHW.reducedTestLiftCLMLeft m d φ χ₁) +
          bvt_W OS lgc (m + 1)
            (BHW.reducedTestLiftCLMLeft m d φ χ₂)
    rw [(BHW.reducedTestLiftCLMLeft m d φ).map_add]
    exact (bvt_W_linear (d := d) OS lgc (m + 1)).map_add _ _
  · intro c χ
    change
      bvt_W OS lgc (m + 1)
          (BHW.reducedTestLiftCLMLeft m d φ (c • χ)) =
        c * bvt_W OS lgc (m + 1)
          (BHW.reducedTestLiftCLMLeft m d φ χ)
    rw [(BHW.reducedTestLiftCLMLeft m d φ).map_smul]
    simpa [smul_eq_mul] using
      (bvt_W_linear (d := d) OS lgc (m + 1)).map_smul c
        (BHW.reducedTestLiftCLMLeft m d φ χ)
  · exact
      (bvt_W_continuous (d := d) OS lgc (m + 1)).comp
        (BHW.reducedTestLiftCLMLeft m d φ).continuous

@[simp] theorem bvt_reducedWightmanCutoffCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (φ : SchwartzNPoint d m)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ χ =
      bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ φ) := by
  rfl

/-- The fixed-reduced-test cutoff functional is translation invariant in the
basepoint cutoff variable. -/
theorem bvt_reducedWightmanCutoffCLM_translation_invariant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (φ : SchwartzNPoint d m) :
    ∀ a : SpacetimeDim d,
      (bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ).comp
          (SCV.translateSchwartzCLM a) =
        bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ := by
  intro a
  ext χ
  rw [ContinuousLinearMap.comp_apply]
  rw [SCV.translateSchwartzCLM_apply]
  rw [bvt_reducedWightmanCutoffCLM_apply,
    bvt_reducedWightmanCutoffCLM_apply]
  rw [← BHW.poincareActSchwartz_translation_eq_translateSchwartz (d := d) a χ]
  have hEq :
      bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ φ) =
        bvt_W OS lgc (m + 1)
          (BHW.reducedTestLift m d
            (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) φ) := by
    exact
      bvt_translation_invariant (d := d) OS lgc (m + 1) a
        (BHW.reducedTestLift m d χ φ)
        (BHW.reducedTestLift m d
          (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) φ)
        (fun x =>
          (BHW.reducedTestLift_translate_uniform
            (d := d) (m := m) χ φ a x).symm)
  exact hEq.symm

/-- The reduced `bvt_W` pairing depends on the basepoint cutoff only through
its total integral. -/
theorem bvt_reducedWightmanCutoff_eq_of_integral_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (φ : SchwartzNPoint d m)
    (χ₁ χ₂ : SchwartzMap (SpacetimeDim d) ℂ)
    (hχ : ∫ x : SpacetimeDim d, χ₁ x = ∫ x : SpacetimeDim d, χ₂ x) :
    bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ₁ φ) =
      bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ₂ φ) := by
  obtain ⟨c, hc⟩ :=
    BHW.schwartzTranslationClassification d
      (bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ)
      (bvt_reducedWightmanCutoffCLM_translation_invariant
        (d := d) OS lgc m φ)
  have hχ₁ :
      bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ χ₁ =
        (c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))) χ₁ := by
    exact congrArg
      (fun L : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ => L χ₁) hc
  have hχ₂ :
      bvt_reducedWightmanCutoffCLM (d := d) OS lgc m φ χ₂ =
        (c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))) χ₂ := by
    exact congrArg
      (fun L : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ => L χ₂) hc
  calc
    bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ₁ φ)
        = c * ∫ x : SpacetimeDim d, χ₁ x := by
          simpa [bvt_reducedWightmanCutoffCLM_apply,
            SchwartzMap.integralCLM_apply, smul_eq_mul] using hχ₁
    _ = c * ∫ x : SpacetimeDim d, χ₂ x := by rw [hχ]
    _ = bvt_W OS lgc (m + 1) (BHW.reducedTestLift m d χ₂ φ) := by
          simpa [bvt_reducedWightmanCutoffCLM_apply,
            SchwartzMap.integralCLM_apply, smul_eq_mul] using hχ₂.symm

/-- The descended reduced Wightman CLM is independent of the chosen normalized
basepoint cutoff. -/
theorem bvt_reducedWightmanCLM_eq_of_cutoff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (χ₁ χ₂ : BHW.NormalizedBasepointCutoff d) :
    bvt_reducedWightmanCLM (d := d) OS lgc χ₁ m =
      bvt_reducedWightmanCLM (d := d) OS lgc χ₂ m := by
  ext φ
  exact
    bvt_reducedWightmanCutoff_eq_of_integral_eq
      (d := d) OS lgc m φ χ₁.toSchwartz χ₂.toSchwartz
      (by rw [χ₁.integral_eq_one, χ₂.integral_eq_one])

/-- The canonical reduced positive-height branch converges to the descended
reduced Wightman CLM. -/
theorem canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ)
    (ψ : SchwartzNPoint d m) :
    Tendsto
      (fun ε : ℝ =>
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * ψ ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m ψ)) := by
  have hBV :=
    bvt_selectedReducedBoundaryValues
      (d := d) OS lgc χ m
      ψ (canonicalReducedDirection (d := d) m)
      (canonicalReducedDirection_mem_productForwardConeReal (d := d) m)
  have hInput :
      (bvt_selectedReducedForwardTubeInput (d := d) OS lgc χ m).toFun =
        bvt_F_reduced (d := d) OS lgc m :=
    bvt_selectedReducedForwardTubeInput_toFun_eq_bvt_F_reduced
      (d := d) OS lgc χ m
  simpa [canonicalReducedBranch, canonicalReducedDirectionC, hInput] using hBV

/-- Boundary value of the adjacent-after-reduced-swap branch.

After the reduced adjacent Jacobian-one change of variables, the
adjacent-after-swap branch is the canonical reduced branch tested against the
reduced real-swap pullback of the test function.  Thus the remaining
Jost/Ruelle locality input is exactly the invariance of this reduced boundary
CLM on compact tests supported in the selected adjacent spacelike edge. -/
theorem canonicalAfterReducedSwapBranch_tendsto_bvt_reducedWightmanCLM_comp
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ : BHW.NormalizedBasepointCutoff d)
    (m : ℕ) (i : Fin (m + 1)) (hi : i.val + 1 < m + 1)
    (φ : SchwartzNPoint d m) :
    Tendsto
      (fun ε : ℝ =>
        ∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            φ ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_reducedWightmanCLM (d := d) OS lgc χ m
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (realPermOnReducedDiffCLE (d := d) m
              (Equiv.swap i ⟨i.val + 1, hi⟩)) φ))) := by
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i ⟨i.val + 1, hi⟩
  let φτ : SchwartzNPoint d m :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realPermOnReducedDiffCLE (d := d) m τ) φ
  have hcanonical :
      Tendsto
        (fun ε : ℝ =>
          ∫ ξ : NPointDomain d m,
            canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_reducedWightmanCLM (d := d) OS lgc χ m φτ)) :=
    canonicalReducedBranch_tendsto_bvt_reducedWightmanCLM
      (d := d) OS lgc χ m φτ
  have heq :
      (fun ε : ℝ =>
        ∫ ξ : NPointDomain d m,
          canonicalAfterReducedSwapBranch
              (d := d) OS lgc m i ⟨i.val + 1, hi⟩ ε ξ *
            φ ξ)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ ξ : NPointDomain d m,
          canonicalReducedBranch (d := d) OS lgc m ε ξ * φτ ξ) := by
    filter_upwards with ε
    rw [integral_canonicalAfterReducedSwapBranch_adjacent_eq_canonicalReducedBranch_comp
      (d := d) OS lgc m i hi ε (φ : NPointDomain d m → ℂ)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    simp [φτ, τ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      realPermOnReducedDiffCLE, realPermOnReducedDiffLinearEquiv]
  simpa [τ, φτ] using Filter.Tendsto.congr' heq.symm hcanonical

end OSReconstruction
