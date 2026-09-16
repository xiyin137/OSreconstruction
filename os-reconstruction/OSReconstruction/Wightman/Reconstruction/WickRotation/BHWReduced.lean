/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/- 
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import Init
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Wightman.NuclearSpaces.ComplexSchwartz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct















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

theorem normalizedCutoffOfBump_hasCompactSupport (d : ℕ) [NeZero d] :
    HasCompactSupport
      ((normalizedCutoffOfBump d).toSchwartz : SpacetimeDim d → ℂ) := by
  unfold normalizedCutoffOfBump
  generalize hspec : spacetimeBump_spec d = S
  rcases S with ⟨_, hcs, hcd, _, _⟩
  dsimp
  set f := spacetimeBump d
  set I := ∫ x : SpacetimeDim d, f x
  set f_schwartz : SchwartzMap (SpacetimeDim d) ℝ := hcs.toSchwartzMap hcd
  have hreal :
      HasCompactSupport
        (fun x : SpacetimeDim d => (f_schwartz x : ℂ)) := by
    convert hcs.comp_left Complex.ofReal_zero using 1 <;> ext x <;> rfl
  have hscaled :
      HasCompactSupport
        (fun x : SpacetimeDim d => (↑I⁻¹ : ℂ) * (f_schwartz x : ℂ)) := by
    change HasCompactSupport
      ((fun _ : SpacetimeDim d => (↑I⁻¹ : ℂ)) *
        fun x : SpacetimeDim d => (f_schwartz x : ℂ))
    exact HasCompactSupport.mul_left hreal
  change HasCompactSupport
    (fun x : SpacetimeDim d => (↑I⁻¹ : ℂ) * (f_schwartz x : ℂ))
  exact hscaled

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
    simpa [realDiffCoordCLE_apply, Fin.succ] using
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

/-- The full reduced real-side Wightman family obtained from a normalized
basepoint cutoff. This is the real distributional input for the reduced BHW
analytic continuation. -/
def reducedWightmanFamily
    (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) :
    (m : ℕ) → SchwartzNPoint d m → ℂ :=
  fun m => reducedWightman Wfn m χ

end BHW
