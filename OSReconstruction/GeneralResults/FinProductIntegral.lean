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

/-- **Bridge: the `finAddProd` inverse equals `Fin.append` componentwise.**

This converts the abstract measure-theoretic equiv used by `finAddProd` into
the concrete `Fin.append` that appears in QFT-side statements like the
cluster integrand `F (Fin.append x y)`. -/
theorem MeasurableEquiv.finAddProd_symm_apply
    {α : Type*} [MeasurableSpace α] (n m : ℕ)
    (x : Fin n → α) (y : Fin m → α) :
    (MeasurableEquiv.finAddProd n m α).symm (x, y) = Fin.append x y := by
  -- `finAddProd = A.trans B` with `A = (piCongrLeft _ finSumFinEquiv).symm`
  -- and `B = sumPiEquivProdPi _`, so `finAddProd.symm (x, y) = A.symm (B.symm (x, y))`
  -- and on indices via finSumFinEquiv this matches Fin.append componentwise.
  have hBsymm :
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α)).symm (x, y) =
        fun (s : Fin n ⊕ Fin m) => Sum.rec (motive := fun _ => α) x y s := by
    rfl
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · -- k = Fin.castAdd m i.  LHS: use piCongrLeft_apply_apply with e = finSumFinEquiv
    --                              and a = inl i, so (e a) = finSumFinEquiv (inl i)
    --                              = Fin.castAdd m i.
    have : (MeasurableEquiv.finAddProd n m α).symm (x, y) (Fin.castAdd m i) = x i := by
      change ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => α) finSumFinEquiv)
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α)).symm (x, y)))
          (Fin.castAdd m i) = x i
      rw [MeasurableEquiv.coe_piCongrLeft, hBsymm]
      have hcast : Fin.castAdd m i = finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin m) := by
        simp [finSumFinEquiv_apply_left]
      rw [hcast, Equiv.piCongrLeft_apply_apply]
    simpa [Fin.append_left] using this
  · -- k = Fin.natAdd n j.
    have : (MeasurableEquiv.finAddProd n m α).symm (x, y) (Fin.natAdd n j) = y j := by
      change ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => α) finSumFinEquiv)
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α)).symm (x, y)))
          (Fin.natAdd n j) = y j
      rw [MeasurableEquiv.coe_piCongrLeft, hBsymm]
      have hnat : Fin.natAdd n j = finSumFinEquiv (Sum.inr j : Fin n ⊕ Fin m) := by
        simp [finSumFinEquiv_apply_right]
      rw [hnat, Equiv.piCongrLeft_apply_apply]
    simpa [Fin.append_right] using this

/-- **Fubini for Fin-indexed products, `Fin.append` form.** Direct QFT-side
statement: an integral over `Fin (n + m) → α` splits via `Fin.append`:

  `∫ z, f z = ∫ x, ∫ y, f (Fin.append x y)`

Convenient for splitting (n+m)-point integrals where the downstream code
uses `Fin.append` to build the joint configuration (as in BHW cluster
integrands). -/
theorem integral_fin_append_split (n m : ℕ) (f : (Fin (n + m) → α) → E)
    (hf : Integrable f (volume : Measure (Fin (n + m) → α))) :
    ∫ z, f z = ∫ x : Fin n → α, ∫ y : Fin m → α, f (Fin.append x y) := by
  rw [integral_fin_add_split n m f hf]
  simp_rw [MeasurableEquiv.finAddProd_symm_apply]

end
