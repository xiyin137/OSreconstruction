/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.ReducedPermutationGluing








noncomputable section

namespace BHW

variable {d n : ℕ}

/-- Reduced BHW continuation from the unchanged reduced Wightman input. -/
theorem reduced_bargmann_hall_wightman_of_input
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ∃ (F_ext : ReducedNPointConfig d m → ℂ),
      DifferentiableOn ℂ F_ext (ReducedPermutedExtendedTubeN d m) ∧
      (∀ η ∈ ReducedForwardTubeN d m, F_ext η = hInput.toFun η) ∧
      IsReducedLorentzInvariant (d := d) (n := m + 1) F_ext ∧
      IsReducedPermutationInvariant (d := d) (n := m + 1) F_ext ∧
      (∀ (G : ReducedNPointConfig d m → ℂ),
        DifferentiableOn ℂ G (ReducedPermutedExtendedTubeN d m) →
        (∀ η ∈ ReducedForwardTubeN d m, G η = hInput.toFun η) →
        ∀ η ∈ ReducedPermutedExtendedTubeN d m, G η = F_ext η) :=
  reducedBHW_of_input_proved Wfn χ m hInput

/-- Chosen reduced BHW extension associated to a bundled reduced forward-tube
datum. -/
noncomputable def W_analytic_BHW_reduced_of_input
    [NeZero d] (Wfn : WightmanFunctions d) (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ReducedBHWExtensionData (d := d) (n := m + 1) hInput.toFun := by
  let h := reduced_bargmann_hall_wightman_of_input (d := d) Wfn χ m hInput
  exact
    { toFun := h.choose
      holomorphic := by
        simpa [ReducedPermutedExtendedTubeN] using h.choose_spec.1
      agrees_on_reducedForwardTube := by
        simpa [ReducedForwardTubeN] using h.choose_spec.2.1
      lorentz_invariant := h.choose_spec.2.2.1
      perm_invariant := h.choose_spec.2.2.2.1 }

/-- Chosen reduced BHW extension in the Route 1 setting, built from a reduced
analytic datum for the canonical reduced Wightman family. -/
noncomputable def route1ReducedBHWExtension
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    ReducedBHWExtensionData (d := d) (n := m + 1) hInput.toFun :=
  W_analytic_BHW_reduced_of_input (d := d) Wfn χ hInput

/-- The Route 1 absolute extension obtained by pulling a bundled reduced
analytic datum back along `reducedDiffMap`. This is the form that should later
replace the old absolute translation proof backend. -/
noncomputable def route1AbsoluteBHWExtension
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  pullbackReducedExtension (d := d) (n := m + 1)
    (route1ReducedBHWExtension (d := d) Wfn χ hInput).toFun

/-- Final Route 1 translation invariance wrapper for a bundled reduced analytic
input. This is the theorem shape the old overlap-connectedness proof should be
replaced by once the reduced analytic input is instantiated. -/
theorem route1AbsoluteBHWExtension_translate
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) {m : ℕ}
    (hInput : Route1ReducedAnalyticInput Wfn χ m)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    route1AbsoluteBHWExtension (d := d) Wfn χ hInput
        (fun k μ => z k μ + c μ) =
      route1AbsoluteBHWExtension (d := d) Wfn χ hInput z := by
  exact reduced_pullback_translation_invariant (d := d) (n := m + 1)
    (route1ReducedBHWExtension (d := d) Wfn χ hInput).toFun z c

/-- Fully packaged Route 1 absolute extension built from `Wfn` and a normalized
basepoint cutoff, using the proved canonical reduced input. -/
noncomputable def route1AbsoluteBHWExtensionCanonical
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ) :
    (Fin (m + 1) → Fin (d + 1) → ℂ) → ℂ :=
  route1AbsoluteBHWExtension (d := d) Wfn χ
    (route1ReducedAnalyticInputExists (d := d) Wfn χ m)

/-- Canonical complex translation invariance through reduced coordinates. -/
theorem route1AbsoluteBHWExtensionCanonical_translate
    [NeZero d] (Wfn : WightmanFunctions d)
    (χ : NormalizedBasepointCutoff d) (m : ℕ)
    (z : Fin (m + 1) → Fin (d + 1) → ℂ) (c : Fin (d + 1) → ℂ) :
    route1AbsoluteBHWExtensionCanonical (d := d) Wfn χ m
        (fun k μ => z k μ + c μ) =
      route1AbsoluteBHWExtensionCanonical (d := d) Wfn χ m z := by
  exact route1AbsoluteBHWExtension_translate (d := d) Wfn χ
    (route1ReducedAnalyticInputExists (d := d) Wfn χ m) z c

end BHW
