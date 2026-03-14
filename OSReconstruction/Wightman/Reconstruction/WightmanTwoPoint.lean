import OSReconstruction.Wightman.Reconstruction.SchwingerOS

open scoped Topology

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Pull back a spacetime Schwartz test by the global sign map `x ↦ -x`. -/
def negSchwartzSpacetime (f : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := SpacetimeDim d)) f

@[simp] theorem negSchwartzSpacetime_apply
    (f : SchwartzSpacetime d) (x : SpacetimeDim d) :
    negSchwartzSpacetime (d := d) f x = f (-x) := rfl

theorem integral_negSchwartzSpacetime_eq (χ : SchwartzSpacetime d) :
    ∫ x : SpacetimeDim d, negSchwartzSpacetime (d := d) χ x =
      ∫ x : SpacetimeDim d, χ x := by
  have hneg_pres :
      MeasureTheory.MeasurePreserving
        (fun x : SpacetimeDim d => -x) MeasureTheory.volume MeasureTheory.volume := by
    classical
    rw [show (fun x : SpacetimeDim d => -x) =
        (fun (x : SpacetimeDim d) (i : Fin (d + 1)) => Neg.neg (x i)) by
        funext x i
        rfl]
    exact MeasureTheory.volume_preserving_pi (fun _ : Fin (d + 1) => by
      simpa using
        (MeasureTheory.Measure.measurePreserving_neg
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
  have hcomp :
      (fun x : SpacetimeDim d => negSchwartzSpacetime (d := d) χ x) =
        (fun x : SpacetimeDim d => χ (-x)) := by
    funext x
    simp [negSchwartzSpacetime]
  rw [hcomp]
  simpa using
    (hneg_pres.integral_comp' (f := {
      toEquiv := Equiv.neg (SpacetimeDim d)
      measurable_toFun := hneg_pres.measurable
      measurable_invFun := hneg_pres.measurable })
      (g := fun x : SpacetimeDim d => χ x))

/-- Pull back a two-point Schwartz test by the global sign map `x ↦ -x`. -/
def negSchwartzNPointTwo (f : SchwartzNPoint d 2) : SchwartzNPoint d 2 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := NPointDomain d 2)) f

@[simp] theorem negSchwartzNPointTwo_apply
    (f : SchwartzNPoint d 2) (x : NPointDomain d 2) :
    negSchwartzNPointTwo (d := d) f x = f (-x) := rfl

/-- The two-point center/difference lift intertwines the global sign map with sign
reversal on the center and difference Schwartz factors. -/
theorem neg_twoPointDifferenceLift
    (χ h : SchwartzSpacetime d) :
    negSchwartzNPointTwo (d := d) (twoPointDifferenceLift χ h) =
      twoPointDifferenceLift
        (negSchwartzSpacetime (d := d) χ)
        (negSchwartzSpacetime (d := d) h) := by
  ext x
  have hdiff : (-x 1) - (-x 0) = -(x 1 - x 0) := by
    abel_nf
  simp [twoPointDifferenceLift_apply, negSchwartzNPointTwo, negSchwartzSpacetime, hdiff]

/-- Continuous linear family of two-point center/difference lifts with the difference test fixed
in the second slot. -/
def twoPointDifferenceLiftLeftCLM (h : SchwartzSpacetime d) :
    SchwartzSpacetime d →L[ℂ] SchwartzNPoint d 2 :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (twoPointCenterDiffCLE d).symm).comp
    (SchwartzMap.prependFieldCLMLeft (onePointToFin1CLM d h))

@[simp] theorem twoPointDifferenceLiftLeftCLM_apply
    (h χ : SchwartzSpacetime d) :
    twoPointDifferenceLiftLeftCLM (d := d) h χ = twoPointDifferenceLift χ h := by
  rfl

namespace WightmanFunctions

/-- For two-point center/difference test functions, Wightman translation invariance acts only
on the center variable. -/
theorem twoPointDifferenceLift_translation_invariant
    (Wfn : WightmanFunctions d) (a : SpacetimeDim d)
    (χ h : SchwartzSpacetime d) :
    Wfn.W 2 (twoPointDifferenceLift χ h) =
      Wfn.W 2 (twoPointDifferenceLift (SCV.translateSchwartz a χ) h) := by
  refine Wfn.translation_invariant 2 a
    (twoPointDifferenceLift χ h)
    (twoPointDifferenceLift (SCV.translateSchwartz a χ) h) ?_
  exact twoPointDifferenceLift_translate_center a χ h

/-- Two-point Wightman reduction: the center/difference pairing depends only on
the difference-variable test. -/
theorem exists_const_twoPointDifferenceLift_eq_integral
    (Wfn : WightmanFunctions d) (h : SchwartzSpacetime d) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      Wfn.W 2 (twoPointDifferenceLift χ h) = c * ∫ x : SpacetimeDim d, χ x := by
  let W : SchwartzNPoint d 2 →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := Wfn.W 2
          map_add' := (Wfn.linear 2).map_add
          map_smul' := (Wfn.linear 2).map_smul }
      cont := Wfn.tempered 2 }
  let T : SchwartzSpacetime d →L[ℂ] ℂ :=
    W.comp (twoPointDifferenceLiftLeftCLM (d := d) h)
  obtain ⟨c, hc⟩ := OSReconstruction.exists_eq_const_integralCLM_of_translationInvariant T (by
    intro a
    ext χ
    exact (WightmanFunctions.twoPointDifferenceLift_translation_invariant
      (Wfn := Wfn) (a := a) (χ := χ) (h := h)).symm)
  refine ⟨c, ?_⟩
  intro χ
  have hχ : T χ =
      (c • (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))) χ := by
    exact congrArg (fun L : SchwartzSpacetime d →L[ℂ] ℂ => L χ) hc
  simpa [T, W, twoPointDifferenceLiftLeftCLM_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.integralCLM_apply, smul_eq_mul] using hχ

/-- The same two-point center/difference reduction after the global sign map. -/
theorem exists_const_neg_twoPointDifferenceLift_eq_integral
    (Wfn : WightmanFunctions d) (h : SchwartzSpacetime d) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      Wfn.W 2 (negSchwartzNPointTwo (d := d) (twoPointDifferenceLift χ h)) =
        c * ∫ x : SpacetimeDim d, χ x := by
  obtain ⟨c, hc⟩ :=
    exists_const_twoPointDifferenceLift_eq_integral
      (d := d) Wfn (negSchwartzSpacetime (d := d) h)
  refine ⟨c, ?_⟩
  intro χ
  have hneg := hc (negSchwartzSpacetime (d := d) χ)
  have hneg' :
      Wfn.W 2 (negSchwartzNPointTwo (d := d) (twoPointDifferenceLift χ h)) =
        c * ∫ x : SpacetimeDim d, negSchwartzSpacetime (d := d) χ x := by
    simpa [neg_twoPointDifferenceLift] using hneg
  rw [integral_negSchwartzSpacetime_eq] at hneg'
  exact hneg'

/-- Two-point reality after the rapidity-reduced partner term reduces to a comparison
between the constants attached to `h` and `-h`. This isolates the exact sign gap. -/
theorem exists_twoPoint_sign_gap_constants
    (Wfn : WightmanFunctions d) (h : SchwartzSpacetime d) :
    ∃ c cneg : ℂ,
      (∀ χ : SchwartzSpacetime d,
        Wfn.W 2 (twoPointDifferenceLift χ h) = c * ∫ x : SpacetimeDim d, χ x) ∧
      (∀ χ : SchwartzSpacetime d,
        Wfn.W 2 (negSchwartzNPointTwo (d := d) (twoPointDifferenceLift χ h)) =
          cneg * ∫ x : SpacetimeDim d, χ x) := by
  obtain ⟨c, hc⟩ :=
    exists_const_twoPointDifferenceLift_eq_integral
      (d := d) Wfn h
  obtain ⟨cneg, hcneg⟩ :=
    exists_const_neg_twoPointDifferenceLift_eq_integral
      (d := d) Wfn h
  exact ⟨c, cneg, hc, hcneg⟩

end WightmanFunctions

end OSReconstruction
