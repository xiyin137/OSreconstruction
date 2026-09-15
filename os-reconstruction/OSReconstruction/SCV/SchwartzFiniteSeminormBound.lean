/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Mathlib429Compat
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.DistributionalUniqueness
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic









noncomputable section

open Filter Topology
open scoped Classical

namespace SCV

/-- The real- and complex-scalar Schwartz seminorm families agree on
complex-valued Schwartz maps, hence so do their finite suprema.  Keeping this
at the finite-family level avoids repeating scalar-conversion inductions at
every continuous Schwartz-map transport. -/
theorem finsetSup_schwartzSeminormFamily_real_eq_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset (Nat × Nat))
    (phi : SchwartzMap E Complex) :
    (s.sup (schwartzSeminormFamily Real E Complex)) phi =
      (s.sup (schwartzSeminormFamily Complex E Complex)) phi := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha_eq :
          (schwartzSeminormFamily Real E Complex a) phi =
            (schwartzSeminormFamily Complex E Complex a) phi := by
        cases a
        rfl
      simp [Finset.sup_insert, ih, ha_eq]

end SCV

namespace OSReconstruction

/-- A continuous linear map between Schwartz spaces transports a finite
family of real Schwartz seminorms to a finite family of source seminorms. -/
theorem exists_schwartzCLM_finsetRealSeminormBound_between
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (T : SchwartzMap E Complex →L[Complex] SchwartzMap F Complex)
    (t : Finset (Nat × Nat)) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 ≤ C ∧
      ∀ phi : SchwartzMap E Complex,
        t.sup (schwartzSeminormFamily Real F Complex) (T phi) ≤
          C * s.sup (schwartzSeminormFamily Real E Complex) phi := by
  let q : Seminorm Real (SchwartzMap E Complex) :=
    (t.sup (schwartzSeminormFamily Real F Complex)).comp
      (T.restrictScalars Real).toLinearMap
  have hq_cont : Continuous q := by
    change Continuous fun phi : SchwartzMap E Complex =>
      t.sup (schwartzSeminormFamily Real F Complex) (T phi)
    exact
      (((schwartz_withSeminorms Real F Complex).finset_sups
        ).continuous_seminorm t).comp T.continuous
  obtain ⟨s, C, _hC_ne, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms Real E Complex) q hq_cont
  refine ⟨s, (C : Real), C.2, ?_⟩
  intro phi
  simpa [q, NNReal.smul_def] using hbound phi

end OSReconstruction
