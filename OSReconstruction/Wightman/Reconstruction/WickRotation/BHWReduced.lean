/- 
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.PoincareAction
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.NuclearSpaces.ComplexSchwartz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Reduced BHW Test Lifts

This file provides the real Schwartz-space lift from reduced `(n-1)` difference
variables back to absolute `n`-point test functions, using:

* a Schwartz cutoff in the basepoint variable, and
* the real full difference-coordinate equivalence.

This is the correct replacement for the impossible raw pullback along
`reducedDiffMapReal`: the latter is not proper and does not preserve Schwartz
decay by itself.
-/

noncomputable section

open scoped SchwartzMap

namespace BHW

variable {d : ℕ} [NeZero d]

/-- Translation-invariant continuous linear functionals on spacetime Schwartz
space are multiples of the Lebesgue integral. This is the remaining analytic
input needed to make the reduced basepoint cutoff completely canonical. -/
def HasSchwartzTranslationClassification (d : ℕ) [NeZero d] : Prop :=
  ∀ T : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ,
    (∀ a : SpacetimeDim d, T.comp (SCV.translateSchwartzCLM a) = T) →
    ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))

/-- Translation-invariant continuous functionals on spacetime Schwartz space
are multiples of the Lebesgue integral. Proved in
`TranslationInvariantSchwartz.lean` via zero-mean decomposition. -/
theorem schwartzTranslationClassification (d : ℕ) [NeZero d] :
    HasSchwartzTranslationClassification d :=
  fun T hT => OSReconstruction.exists_eq_const_integralCLM_of_translationInvariant T hT

/-- A Schwartz cutoff in the absolute basepoint variable normalized to have
integral `1`. Any two such cutoffs define the same reduced functional once the
translation-invariant classification theorem is available. -/
structure NormalizedBasepointCutoff (d : ℕ) [NeZero d] where
  toSchwartz : SchwartzMap (SpacetimeDim d) ℂ
  integral_eq_one : ∫ x : SpacetimeDim d, toSchwartz x = 1

instance : Coe (NormalizedBasepointCutoff d) (SchwartzMap (SpacetimeDim d) ℂ) where
  coe χ := χ.toSchwartz

@[simp] theorem NormalizedBasepointCutoff.coe_mk
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (hχ : ∫ x : SpacetimeDim d, χ x = 1) :
    ((NormalizedBasepointCutoff.mk χ hχ : NormalizedBasepointCutoff d) :
      SchwartzMap (SpacetimeDim d) ℂ) = χ := rfl

/-- A smooth compactly supported nonneg function on spacetime with f(0) = 1,
obtained from Mathlib's `exists_contDiff_tsupport_subset`. -/
private noncomputable def spacetimeBump (d : ℕ) : SpacetimeDim d → ℝ :=
  (exists_contDiff_tsupport_subset (E := SpacetimeDim d) (n := (⊤ : ℕ∞))
    (s := Set.univ) (x := 0) Filter.univ_mem).choose

private lemma spacetimeBump_spec (d : ℕ) :
    tsupport (spacetimeBump d) ⊆ Set.univ ∧
    HasCompactSupport (spacetimeBump d) ∧
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeBump d) ∧
    Set.range (spacetimeBump d) ⊆ Set.Icc 0 1 ∧
    spacetimeBump d 0 = 1 :=
  (exists_contDiff_tsupport_subset (E := SpacetimeDim d) (n := (⊤ : ℕ∞))
    (s := Set.univ) (x := 0) Filter.univ_mem).choose_spec

private lemma spacetimeBump_integral_pos (d : ℕ) [NeZero d] :
    0 < ∫ x : SpacetimeDim d, spacetimeBump d x := by
  have ⟨_, hcs, hcd, hrange, hf0⟩ := spacetimeBump_spec d
  exact hcd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun x => (hrange (Set.mem_range_self x)).1) (by linarith)

/-- Construct a normalized basepoint cutoff from a smooth compactly supported
bump function. The bump function has positive integral (it is nonneg and equals
1 at the origin), so dividing by its integral yields a Schwartz function with
integral exactly 1. -/
noncomputable def normalizedCutoffOfBump (d : ℕ) [NeZero d] :
    NormalizedBasepointCutoff d := by
  have ⟨_, hcs, hcd, _, _⟩ := spacetimeBump_spec d
  set f := spacetimeBump d
  set I := ∫ x : SpacetimeDim d, f x
  have hI_pos := spacetimeBump_integral_pos d
  have hI_ne : (I : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hI_pos)
  set f_schwartz : SchwartzMap (SpacetimeDim d) ℝ := hcs.toSchwartzMap hcd
  set g := (↑I⁻¹ : ℂ) • SchwartzMap.ofRealCLM f_schwartz
  refine ⟨g, ?_⟩
  simp only [g, SchwartzMap.smul_apply, SchwartzMap.ofRealCLM_apply]
  rw [MeasureTheory.integral_smul, smul_eq_mul]
  have hcoe : (fun x => (f_schwartz x : ℂ)) = fun x => (↑(f x) : ℂ) := by
    ext x; rfl
  rw [hcoe]
  have : ∫ x : SpacetimeDim d, (↑(f x) : ℂ) = ↑I :=
    (@RCLike.ofRealLI ℂ _).integral_comp_comm f
  rw [this, Complex.ofReal_inv, inv_mul_cancel₀ hI_ne]

/-- Lift a reduced Schwartz test to absolute coordinates by inserting a
    Schwartz cutoff in the basepoint variable and then composing with the real
    full difference-coordinate chart. -/
noncomputable def reducedTestLift (m d : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    SchwartzNPoint d m →L[ℂ] SchwartzNPoint d (m + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDiffCoordCLE (m + 1) d)).comp
    (SchwartzMap.prependFieldCLMRight (n := m) χ)

@[simp] theorem reducedTestLift_apply (m d : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m) (x : NPointDomain d (m + 1)) :
    reducedTestLift m d χ φ x = χ (x 0) * φ (reducedDiffMapReal (m + 1) d x) := by
  have hhead : (realDiffCoordCLE (m + 1) d) x 0 = x 0 := by
    ext μ
    simp [realDiffCoordCLE_apply]
  have htail :
      (fun i => (realDiffCoordCLE (m + 1) d x) i.succ) =
        reducedDiffMapReal (m + 1) d x := by
    ext j μ
    simpa [realDiffCoordCLE_apply] using
      (reducedDiffMapReal_apply (m + 1) d x j μ).symm
  calc
    reducedTestLift m d χ φ x
        = χ ((realDiffCoordCLE (m + 1) d) x 0) *
            φ (fun i => (realDiffCoordCLE (m + 1) d x) i.succ) := by
              simp [reducedTestLift]
    _ = χ (x 0) * φ (fun i => (realDiffCoordCLE (m + 1) d x) i.succ) := by
          rw [hhead]
    _ = χ (x 0) * φ (reducedDiffMapReal (m + 1) d x) := by
          have hphi :
              φ (fun i => (realDiffCoordCLE (m + 1) d x) i.succ) =
                φ (reducedDiffMapReal (m + 1) d x) := by
            simpa using congrArg φ htail
          rw [hphi]

/-- Internal Route 1 reduced real-side Wightman functional defined using a
    chosen basepoint Schwartz cutoff.

    For reduced arity `m`, this starts from the public literal `(m + 1)`-point
    object `Wfn.W (m + 1)` and tests it against the lifted Schwartz function
    `reducedTestLift m d χ φ`. It is therefore an internal `(m + 1) -> m`
    reduced-coordinate bridge, not a redefinition of the public meaning of
    `Wfn.W n`. -/
def reducedWightmanWithCutoff (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    SchwartzNPoint d m → ℂ :=
  fun φ => Wfn.W (m + 1) (reducedTestLift m d χ φ)

theorem reducedWightmanWithCutoff_continuous (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    Continuous (reducedWightmanWithCutoff Wfn m χ) := by
  simpa [reducedWightmanWithCutoff] using
    (Wfn.tempered (m + 1)).comp (reducedTestLift m d χ).continuous

theorem reducedWightmanWithCutoff_linear (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    IsLinearMap ℂ (reducedWightmanWithCutoff Wfn m χ) := by
  constructor
  · intro φ ψ
    simp [reducedWightmanWithCutoff, (Wfn.linear (m + 1)).map_add]
  · intro c φ
    simp [reducedWightmanWithCutoff, (Wfn.linear (m + 1)).map_smul]

/-- Translating all absolute arguments only translates the basepoint cutoff; the
    reduced difference test is unchanged. -/
theorem reducedTestLift_translate_uniform (m : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ) (φ : SchwartzNPoint d m)
    (a : SpacetimeDim d) (x : NPointDomain d (m + 1)) :
    reducedTestLift m d χ φ (fun k μ => x k μ + a μ) =
      reducedTestLift m d
        (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) φ x := by
  rw [reducedTestLift_apply, reducedTestLift_apply]
  have hdiff :
      reducedDiffMapReal (m + 1) d (fun k μ => x k μ + a μ) =
        reducedDiffMapReal (m + 1) d x :=
    reducedDiffMapReal_translate_uniform_eq (m + 1) d x a
  have hshift0 : (fun μ => x 0 μ + a μ) = x 0 + a := rfl
  have hcut :
      (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) (x 0) = χ (x 0 + a) := by
    have hInv :
        ((PoincareGroup.translation' (-a) : PoincareGroup d)⁻¹ =
          PoincareGroup.translation' a) := by
      ext <;> simp [PoincareGroup.translation']
    simp [poincareActSchwartz_apply, hInv, PoincareGroup.pureTranslation_act]
  rw [hshift0, hcut, hdiff]

/-- The descended reduced real functional is invariant under translating the
    chosen basepoint cutoff. -/
theorem reducedWightmanWithCutoff_translate (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : SchwartzMap (SpacetimeDim d) ℂ)
    (φ : SchwartzNPoint d m) (a : SpacetimeDim d) :
    reducedWightmanWithCutoff Wfn m χ φ =
      reducedWightmanWithCutoff Wfn m
        (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) φ := by
  have hEq :
      Wfn.W (m + 1) (reducedTestLift m d χ φ) =
        Wfn.W (m + 1)
          (reducedTestLift m d
            (poincareActSchwartz (PoincareGroup.translation' (-a)) χ) φ) := by
    apply Wfn.translation_invariant (m + 1) a
    intro x
    exact (reducedTestLift_translate_uniform (m := m) χ φ a x).symm
  simpa [reducedWightmanWithCutoff] using hEq

/-- The `χ`-slot lift of a fixed reduced test `φ` as a continuous linear map. -/
noncomputable def reducedTestLiftCLMLeft (m d : ℕ)
    (φ : SchwartzNPoint d m) :
    SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] SchwartzNPoint d (m + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDiffCoordCLE (m + 1) d)).comp
    (SchwartzMap.prependFieldCLMLeft (n := m) φ)

@[simp] theorem reducedTestLiftCLMLeft_apply (m d : ℕ)
    (φ : SchwartzNPoint d m) (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    reducedTestLiftCLMLeft m d φ χ = reducedTestLift m d χ φ := by
  rfl

/-- The `χ`-slot reduced functional as a continuous linear map. -/
noncomputable def reducedWightmanWithCutoffCLM (Wfn : WightmanFunctions d) (m : ℕ)
    (φ : SchwartzNPoint d m) :
    SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ := by
  refine
    { toLinearMap :=
        { toFun := fun χ => reducedWightmanWithCutoff Wfn m χ φ
          map_add' := by
            intro χ₁ χ₂
            change Wfn.W (m + 1) (reducedTestLiftCLMLeft m d φ (χ₁ + χ₂)) =
              Wfn.W (m + 1) (reducedTestLiftCLMLeft m d φ χ₁) +
                Wfn.W (m + 1) (reducedTestLiftCLMLeft m d φ χ₂)
            rw [(reducedTestLiftCLMLeft m d φ).map_add]
            exact (Wfn.linear (m + 1)).map_add _ _
          map_smul' := by
            intro c χ
            change Wfn.W (m + 1) (reducedTestLiftCLMLeft m d φ (c • χ)) =
              c * Wfn.W (m + 1) (reducedTestLiftCLMLeft m d φ χ)
            rw [(reducedTestLiftCLMLeft m d φ).map_smul]
            simpa [smul_eq_mul] using (Wfn.linear (m + 1)).map_smul c
              (reducedTestLiftCLMLeft m d φ χ) }
      cont := ?_ }
  exact (Wfn.tempered (m + 1)).comp (reducedTestLiftCLMLeft m d φ).continuous

@[simp] theorem reducedWightmanWithCutoffCLM_apply (Wfn : WightmanFunctions d) (m : ℕ)
    (φ : SchwartzNPoint d m) (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    reducedWightmanWithCutoffCLM Wfn m φ χ = reducedWightmanWithCutoff Wfn m χ φ := by
  rfl

/-- Translation of the basepoint cutoff agrees with the ambient Schwartz
    translation on spacetime. -/
theorem poincareActSchwartz_translation_eq_translateSchwartz
    (a : SpacetimeDim d) (χ : SchwartzMap (SpacetimeDim d) ℂ) :
    poincareActSchwartz (PoincareGroup.translation' (-a)) χ =
      SCV.translateSchwartz a χ := by
  ext x
  have hInv :
      ((PoincareGroup.translation' (-a) : PoincareGroup d)⁻¹ =
        PoincareGroup.translation' a) := by
    ext <;> simp [PoincareGroup.translation']
  simp [poincareActSchwartz_apply, hInv, PoincareGroup.pureTranslation_act,
    SCV.translateSchwartz_apply]

/-- For fixed reduced test `φ`, the cutoff functional is translation-invariant
    in the Schwartz sense. -/
theorem reducedWightmanWithCutoffCLM_translation_invariant
    (Wfn : WightmanFunctions d) (m : ℕ) (φ : SchwartzNPoint d m) :
    ∀ a : SpacetimeDim d,
      (reducedWightmanWithCutoffCLM Wfn m φ).comp (SCV.translateSchwartzCLM a) =
        reducedWightmanWithCutoffCLM Wfn m φ := by
  intro a
  ext χ
  rw [ContinuousLinearMap.comp_apply]
  rw [SCV.translateSchwartzCLM_apply]
  rw [reducedWightmanWithCutoffCLM_apply, reducedWightmanWithCutoffCLM_apply]
  rw [← poincareActSchwartz_translation_eq_translateSchwartz (d := d) a χ]
  exact (reducedWightmanWithCutoff_translate (Wfn := Wfn) (m := m)
    (χ := χ) (φ := φ) (a := a)).symm

/-- Conditional Route 1 reduction: once translation-invariant continuous
    functionals on spacetime Schwartz space are classified by the Lebesgue
    integral, the cutoff dependence of the reduced functional is only through
    `∫ χ`. -/
theorem exists_const_reducedWightmanWithCutoff_eq_integral_of_classification
    (hclass :
      ∀ T : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ,
        (∀ a : SpacetimeDim d, T.comp (SCV.translateSchwartzCLM a) = T) →
        ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))
    (Wfn : WightmanFunctions d) (m : ℕ) (φ : SchwartzNPoint d m) :
    ∃ c : ℂ, ∀ χ : SchwartzMap (SpacetimeDim d) ℂ,
      reducedWightmanWithCutoff Wfn m χ φ = c * ∫ x : SpacetimeDim d, χ x := by
  obtain ⟨c, hc⟩ := hclass
    (reducedWightmanWithCutoffCLM Wfn m φ)
    (reducedWightmanWithCutoffCLM_translation_invariant (Wfn := Wfn) (m := m) (φ := φ))
  refine ⟨c, ?_⟩
  intro χ
  have hχ :
      reducedWightmanWithCutoffCLM Wfn m φ χ =
        (c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))) χ := by
    exact congrArg (fun L : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ => L χ) hc
  simpa [reducedWightmanWithCutoffCLM_apply, SchwartzMap.integralCLM_apply,
    smul_eq_mul] using hχ

/-- Under the translation-invariant classification hypothesis, the reduced
    functional depends on the cutoff only through its integral. -/
theorem reducedWightmanWithCutoff_eq_of_integral_eq_of_classification
    (hclass :
      ∀ T : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ,
        (∀ a : SpacetimeDim d, T.comp (SCV.translateSchwartzCLM a) = T) →
        ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))
    (Wfn : WightmanFunctions d) (m : ℕ) (φ : SchwartzNPoint d m)
    (χ₁ χ₂ : SchwartzMap (SpacetimeDim d) ℂ)
    (hχ : ∫ x : SpacetimeDim d, χ₁ x = ∫ x : SpacetimeDim d, χ₂ x) :
    reducedWightmanWithCutoff Wfn m χ₁ φ =
      reducedWightmanWithCutoff Wfn m χ₂ φ := by
  obtain ⟨c, hc⟩ :=
    exists_const_reducedWightmanWithCutoff_eq_integral_of_classification
      hclass Wfn m φ
  rw [hc χ₁, hc χ₂, hχ]

/-- In particular, normalized cutoffs are interchangeable. -/
theorem reducedWightmanWithCutoff_eq_of_integral_one_of_classification
    (hclass :
      ∀ T : SchwartzMap (SpacetimeDim d) ℂ →L[ℂ] ℂ,
        (∀ a : SpacetimeDim d, T.comp (SCV.translateSchwartzCLM a) = T) →
        ∃ c : ℂ, T = c • (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d))))
    (Wfn : WightmanFunctions d) (m : ℕ) (φ : SchwartzNPoint d m)
    (χ₁ χ₂ : SchwartzMap (SpacetimeDim d) ℂ)
    (hχ₁ : ∫ x : SpacetimeDim d, χ₁ x = 1)
    (hχ₂ : ∫ x : SpacetimeDim d, χ₂ x = 1) :
    reducedWightmanWithCutoff Wfn m χ₁ φ =
      reducedWightmanWithCutoff Wfn m χ₂ φ := by
  apply reducedWightmanWithCutoff_eq_of_integral_eq_of_classification
    hclass Wfn m φ χ₁ χ₂
  rw [hχ₁, hχ₂]

/-- The reduced real-side Wightman functional defined using a normalized
basepoint cutoff. Under the classification hypothesis below, this is
independent of the chosen normalized cutoff. -/
def reducedWightman
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) :
    SchwartzNPoint d m → ℂ :=
  reducedWightmanWithCutoff Wfn m χ.toSchwartz

@[simp] theorem reducedWightman_apply
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) (φ : SchwartzNPoint d m) :
    reducedWightman Wfn m χ φ =
      reducedWightmanWithCutoff Wfn m χ.toSchwartz φ := by
  rfl

theorem reducedWightman_continuous
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) :
    Continuous (reducedWightman Wfn m χ) := by
  simpa [reducedWightman] using
    reducedWightmanWithCutoff_continuous (Wfn := Wfn) (m := m) χ.toSchwartz

theorem reducedWightman_linear
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) :
    IsLinearMap ℂ (reducedWightman Wfn m χ) := by
  simpa [reducedWightman] using
    reducedWightmanWithCutoff_linear (Wfn := Wfn) (m := m) χ.toSchwartz

/-- The reduced real-side Wightman functional as a continuous linear map in the
reduced test variable. -/
noncomputable def reducedWightmanCLM
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) :
    SchwartzNPoint d m →L[ℂ] ℂ := by
  refine
    { toLinearMap :=
        { toFun := reducedWightman Wfn m χ
          map_add' := by
            intro φ ψ
            change Wfn.W (m + 1) (reducedTestLift m d χ.toSchwartz (φ + ψ)) =
              Wfn.W (m + 1) (reducedTestLift m d χ.toSchwartz φ) +
                Wfn.W (m + 1) (reducedTestLift m d χ.toSchwartz ψ)
            rw [(reducedTestLift m d χ.toSchwartz).map_add]
            exact (Wfn.linear (m + 1)).map_add _ _
          map_smul' := by
            intro c φ
            change Wfn.W (m + 1) (reducedTestLift m d χ.toSchwartz (c • φ)) =
              c * Wfn.W (m + 1) (reducedTestLift m d χ.toSchwartz φ)
            rw [(reducedTestLift m d χ.toSchwartz).map_smul]
            simpa [smul_eq_mul] using (Wfn.linear (m + 1)).map_smul c
              (reducedTestLift m d χ.toSchwartz φ) }
      cont := ?_ }
  exact (Wfn.tempered (m + 1)).comp (reducedTestLift m d χ.toSchwartz).continuous

@[simp] theorem reducedWightmanCLM_apply
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ : NormalizedBasepointCutoff d) (φ : SchwartzNPoint d m) :
    reducedWightmanCLM Wfn m χ φ = reducedWightman Wfn m χ φ := by
  rfl

/-- Once translation-invariant Schwartz functionals are classified by the
Lebesgue integral, the reduced functional is independent of the normalized
basepoint cutoff used to define it. -/
theorem reducedWightman_eq_of_cutoff
    (hclass : HasSchwartzTranslationClassification d)
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) (φ : SchwartzNPoint d m) :
    reducedWightman Wfn m χ₁ φ = reducedWightman Wfn m χ₂ φ := by
  apply reducedWightmanWithCutoff_eq_of_integral_one_of_classification
    hclass Wfn m φ χ₁.toSchwartz χ₂.toSchwartz
  · simpa using χ₁.integral_eq_one
  · simpa using χ₂.integral_eq_one

theorem reducedWightman_eq_of_cutoff_funext
    (hclass : HasSchwartzTranslationClassification d)
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightman Wfn m χ₁ = reducedWightman Wfn m χ₂ := by
  funext φ
  exact reducedWightman_eq_of_cutoff hclass Wfn m χ₁ χ₂ φ

theorem reducedWightman_eq_of_cutoff_canonical
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) (φ : SchwartzNPoint d m) :
    reducedWightman Wfn m χ₁ φ = reducedWightman Wfn m χ₂ φ := by
  exact reducedWightman_eq_of_cutoff
    (schwartzTranslationClassification d) Wfn m χ₁ χ₂ φ

theorem reducedWightman_eq_of_cutoff_funext_canonical
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightman Wfn m χ₁ = reducedWightman Wfn m χ₂ := by
  exact reducedWightman_eq_of_cutoff_funext
    (schwartzTranslationClassification d) Wfn m χ₁ χ₂

theorem reducedWightmanCLM_eq_of_cutoff
    (hclass : HasSchwartzTranslationClassification d)
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightmanCLM Wfn m χ₁ = reducedWightmanCLM Wfn m χ₂ := by
  ext φ
  exact reducedWightman_eq_of_cutoff hclass Wfn m χ₁ χ₂ φ

theorem reducedWightmanCLM_eq_of_cutoff_canonical
    (Wfn : WightmanFunctions d) (m : ℕ)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightmanCLM Wfn m χ₁ = reducedWightmanCLM Wfn m χ₂ := by
  exact reducedWightmanCLM_eq_of_cutoff
    (schwartzTranslationClassification d) Wfn m χ₁ χ₂

/-- The full reduced real-side Wightman family obtained from a normalized
basepoint cutoff. This is the real distributional input for the reduced BHW
analytic continuation. -/
def reducedWightmanFamily
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ :=
  fun m => reducedWightman Wfn m χ

@[simp] theorem reducedWightmanFamily_apply
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (m : ℕ) (φ : SchwartzNPoint d m) :
    reducedWightmanFamily Wfn χ m φ = reducedWightman Wfn m χ φ := by
  rfl

theorem reducedWightmanFamily_continuous
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    Continuous (reducedWightmanFamily Wfn χ m) := by
  simpa [reducedWightmanFamily] using reducedWightman_continuous (Wfn := Wfn) (m := m) χ

theorem reducedWightmanFamily_linear
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    IsLinearMap ℂ (reducedWightmanFamily Wfn χ m) := by
  simpa [reducedWightmanFamily] using reducedWightman_linear (Wfn := Wfn) (m := m) χ

/-- The reduced real-side Wightman family as continuous linear maps in each
reduced Schwartz variable slot. -/
noncomputable def reducedWightmanFamilyCLM
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m →L[ℂ] ℂ :=
  fun m => reducedWightmanCLM Wfn m χ

@[simp] theorem reducedWightmanFamilyCLM_apply
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d)
    (m : ℕ) (φ : SchwartzNPoint d m) :
    reducedWightmanFamilyCLM Wfn χ m φ = reducedWightmanFamily Wfn χ m φ := by
  rfl

theorem reducedWightmanFamily_eq_of_cutoff_canonical
    (Wfn : WightmanFunctions d)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightmanFamily Wfn χ₁ = reducedWightmanFamily Wfn χ₂ := by
  funext m
  exact reducedWightman_eq_of_cutoff_funext_canonical (Wfn := Wfn) (m := m) χ₁ χ₂

theorem reducedWightmanFamilyCLM_eq_of_cutoff_canonical
    (Wfn : WightmanFunctions d)
    (χ₁ χ₂ : NormalizedBasepointCutoff d) :
    reducedWightmanFamilyCLM Wfn χ₁ = reducedWightmanFamilyCLM Wfn χ₂ := by
  funext m
  exact reducedWightmanCLM_eq_of_cutoff_canonical (Wfn := Wfn) (m := m) χ₁ χ₂

end BHW
