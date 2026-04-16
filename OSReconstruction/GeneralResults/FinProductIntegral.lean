/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fubini for Fin-indexed product integrals

Splitting an integral over `Fin (n + m) → α` into an iterated integral
over `(Fin n → α) × (Fin m → α)`.

This combines:
1. `MeasurePreserving.piCongrLeft` for the reindexing `Fin n ⊕ Fin m ≃ Fin (n + m)`
2. `MeasurableEquiv.sumPiEquivProdPi` for splitting `(Fin n ⊕ Fin m → α) ≃ (Fin n → α) × (Fin m → α)`
3. `integral_prod` (Fubini) for the product splitting

## Main results

* `integral_fin_add_split` — the main Fubini splitting theorem

## References

Standard measure theory. Used in the OS reconstruction for splitting
(n+m)-point Schwinger/Wightman integrals into n-point × m-point factors.
-/

noncomputable section

open MeasureTheory MeasurableSpace

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The measurable equivalence `(Fin (n + m) → α) ≃ᵐ (Fin n → α) × (Fin m → α)`.
    Combines `finSumFinEquiv` reindexing with the sum-pi splitting. -/
noncomputable def MeasurableEquiv.finAddProd (n m : ℕ) (α : Type*) [MeasurableSpace α] :
    (Fin (n + m) → α) ≃ᵐ (Fin n → α) × (Fin m → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => α) finSumFinEquiv).symm |>.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α))

/-- The `finAddProd` equivalence preserves volume (Lebesgue measure). -/
theorem MeasureTheory.volume_preserving_finAddProd (n m : ℕ) (α : Type*)
    [MeasureSpace α] [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (MeasurableEquiv.finAddProd n m α) volume volume := by
  unfold MeasurableEquiv.finAddProd
  exact MeasurePreserving.trans
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => α) finSumFinEquiv).symm)
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α))

/-- **Fubini for Fin-indexed products.** An integral over `Fin (n + m) → α` splits
    as an iterated integral over `Fin n → α` and `Fin m → α`:

    `∫ z, f z = ∫ x, ∫ y, f (finAddProd⁻¹ (x, y))`

    This is the key tool for splitting (n+m)-point QFT integrals into
    n-point × m-point factors. -/
theorem integral_fin_add_split (n m : ℕ) (f : (Fin (n + m) → α) → E)
    (hf : Integrable f (volume : Measure (Fin (n + m) → α))) :
    ∫ z, f z = ∫ x : Fin n → α, ∫ y : Fin m → α,
      f ((MeasurableEquiv.finAddProd n m α).symm (x, y)) := by
  let e := MeasurableEquiv.finAddProd n m α
  have hpres : MeasurePreserving e volume volume := volume_preserving_finAddProd n m α
  have hcomp : ∫ p : (Fin n → α) × (Fin m → α), f (e.symm p) = ∫ z, f z := by
    simpa [e] using hpres.symm.integral_comp' f
  have hf' : Integrable (fun p : (Fin n → α) × (Fin m → α) => f (e.symm p)) volume := by
    simpa [Function.comp, e] using hpres.symm.integrable_comp_of_integrable hf
  calc
    ∫ z, f z = ∫ p : (Fin n → α) × (Fin m → α), f (e.symm p) := by
      simpa using hcomp.symm
    _ = ∫ x : Fin n → α, ∫ y : Fin m → α, f (e.symm (x, y)) := by
      simpa [e] using
        (integral_prod
          (μ := (volume : Measure (Fin n → α)))
          (ν := (volume : Measure (Fin m → α)))
          (f := fun p : (Fin n → α) × (Fin m → α) => f (e.symm p)) hf')

end
