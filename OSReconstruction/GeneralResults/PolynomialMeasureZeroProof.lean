/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proof: Zero Sets of Real Polynomials Have Lebesgue Measure Zero

This file proves `MvPolynomial.volume_zeroSet_eq_zero` from scratch,
eliminating the axiom in `PolynomialMeasureZero.lean`.

The proof is by induction on the number of variables n:
- n=0: single point, nonzero constant → empty zero set
- n→n+1: Fubini slice + IH on leading coefficient's zero set

## Architecture

1. **Univariate case** (`Polynomial.volume_zeroSet_eq_zero`):
   nonzero polynomial has finitely many roots → measure zero

2. **Measurability** (`MvPolynomial.measurableSet_zeroSet`):
   zero set is closed (preimage of {0} under continuous eval) → measurable

3. **Fubini slice** (`volume_piFinSucc_null`):
   if a.e. 1D slice has measure zero, total volume is zero

4. **Main induction** (`MvPolynomial.volume_zeroSet_eq_zero_proved`):
   split first variable via `finSuccEquiv`, apply IH + univariate case

## References

- Bochnak-Coste-Roy, "Real Algebraic Geometry", Proposition 2.8.2
- Caron-Traynor (1971), Okamoto (1973)
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.MvPolynomial

open MeasureTheory MvPolynomial Polynomial
open scoped Polynomial

noncomputable section

/-! ### Step 1: The Univariate Case -/

/-- A nonzero univariate polynomial has a zero set of Lebesgue measure zero.
    The zero set is contained in `p.roots.toFinset`, which is finite. -/
lemma Polynomial.volume_zeroSet_eq_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    volume {x : ℝ | p.eval x = 0} = 0 := by
  have h_subset : {x : ℝ | p.eval x = 0} ⊆ ↑p.roots.toFinset := by
    intro x hx
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset] at hx ⊢
    exact (Polynomial.mem_roots hp).mpr hx
  exact measure_mono_null h_subset (Finset.measure_zero _ _)

/-! ### Step 2: Measurability -/

/-- The zero set of any multivariate polynomial is measurable (Borel).
    It is the preimage of {0} under the continuous evaluation map. -/
lemma MvPolynomial.measurableSet_zeroSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MeasurableSet {x : Fin n → ℝ | eval x p = 0} := by
  -- eval is continuous (polynomial → continuous), {0} is closed
  exact isClosed_eq (MvPolynomial.continuous_eval p) continuous_const |>.measurableSet

/-! ### Step 3: Fubini Slice for Null Sets -/

/-- If a.e. 1D slice of a measurable set in ℝⁿ⁺¹ has measure zero,
    then the set has (n+1)-dimensional measure zero.
    Uses `Fin.cons` convention matching `MeasurableEquiv.piFinSucc`. -/
lemma volume_piFinSucc_null {n : ℕ} (S : Set (Fin (n + 1) → ℝ))
    (hS_meas : MeasurableSet S)
    (h_ae : ∀ᵐ (x : Fin n → ℝ) ∂volume, volume {t : ℝ | Fin.cons t x ∈ S} = 0) :
    volume S = 0 := by
  -- Transfer to product space via piFinSuccAbove at index 0
  -- piFinSuccAbove 0 : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)
  -- maps f ↦ (f 0, f ∘ Fin.succ)
  -- inverse maps (t, x) ↦ Fin.cons t x
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  let T : Set (ℝ × (Fin n → ℝ)) := e '' S
  have hT_meas : MeasurableSet T := e.measurableSet_image.mpr hS_meas
  -- volume S = volume T (via measure preservation)
  have h_eq : volume S = volume T := by
    have := hmp.map_eq
    rw [← this]
    rw [Measure.map_apply e.measurable hT_meas]
    exact congr_arg _ (e.preimage_image S).symm
  rw [h_eq]
  -- Key identity: e.symm (t, x) = Fin.cons t x
  have h_symm : ∀ (t : ℝ) (x : Fin n → ℝ), e.symm (t, x) = Fin.cons t x := by
    intro t x
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    funext i; exact Fin.consEquiv_apply _ _ i
  -- Hence (t, x) ∈ T ↔ Fin.cons t x ∈ S
  have h_mem : ∀ (t : ℝ) (x : Fin n → ℝ), (t, x) ∈ T ↔ Fin.cons t x ∈ S := by
    intro t x
    simp only [T, Set.mem_image]
    constructor
    · rintro ⟨f, hfS, hfe⟩
      rwa [← h_symm t x, ← hfe, e.symm_apply_apply]
    · intro hS
      exact ⟨Fin.cons t x, hS, by rw [← h_symm t x]; exact e.apply_symm_apply _⟩
  -- Write volume T as iterated integral via Tonelli (swapped order)
  rw [← lintegral_indicator_one hT_meas]
  have hf : Measurable (T.indicator (1 : ℝ × (Fin n → ℝ) → ENNReal)) :=
    measurable_const.indicator hT_meas
  have hvol : (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume := rfl
  rw [hvol, lintegral_prod_symm' _ hf]
  -- Goal: ∫⁻ x, ∫⁻ t, T.indicator 1 (t, x) ∂vol ∂vol = 0
  trans ∫⁻ (_ : Fin n → ℝ), (0 : ENNReal) ∂volume
  · apply lintegral_congr_ae
    refine h_ae.mono fun x hx => ?_
    -- hx : volume {t | Fin.cons t x ∈ S} = 0
    have h_meas_slice : MeasurableSet {t : ℝ | (t, x) ∈ T} :=
      hT_meas.preimage (measurable_id.prodMk measurable_const)
    -- Convert inner integral to measure of slice
    show ∫⁻ (t : ℝ), T.indicator (1 : ℝ × (Fin n → ℝ) → ENNReal) (t, x) ∂volume = 0
    rw [show ∫⁻ (t : ℝ), T.indicator (1 : ℝ × (Fin n → ℝ) → ENNReal) (t, x) ∂volume =
        volume {t : ℝ | (t, x) ∈ T} from by
      rw [← lintegral_indicator_one h_meas_slice]
      congr 1]
    -- {t | (t, x) ∈ T} = {t | Fin.cons t x ∈ S}
    rw [show {t : ℝ | (t, x) ∈ T} = {t : ℝ | Fin.cons t x ∈ S} from by
      ext t; exact h_mem t x]
    exact hx
  · simp

/-! ### Step 4: The Main Induction -/

/-- **The zero set of a nonzero multivariate polynomial has Lebesgue measure zero.**
    Proved by induction on the number of variables. -/
theorem MvPolynomial.volume_zeroSet_eq_zero_proved (n : ℕ) :
    ∀ (p : MvPolynomial (Fin n) ℝ) (_ : p ≠ 0),
      volume {x : Fin n → ℝ | eval x p = 0} = 0 := by
  induction n with
  | zero =>
    intro p hp
    -- Fin 0 → ℝ is a single point. Since p ≠ 0, it evaluates to a nonzero
    -- constant, so the zero set is empty.
    have h_empty : {x : Fin 0 → ℝ | (eval x) p = 0} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x
      simp only [Set.mem_setOf_eq]
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      simp only [MvPolynomial.eval_zero]
      intro h_eval
      apply hp
      ext d
      have : d = 0 := Subsingleton.elim _ _
      subst this
      simp [MvPolynomial.constantCoeff] at h_eval
      exact h_eval
    simp [h_empty, measure_empty]
  | succ n ih =>
    intro p hp
    -- 1. Split first variable via finSuccEquiv
    --    finSuccEquiv : MvPolynomial (Fin (n+1)) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin n) ℝ)
    let q : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (finSuccEquiv ℝ n).injective (show (finSuccEquiv ℝ n) p = (finSuccEquiv ℝ n) 0 from
        by simp only [q] at h; rw [h, map_zero])

    -- 2. Extract a nonzero coefficient
    obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hq (Polynomial.ext (fun i => h i))
    let C := q.coeff k

    -- 3. By IH, the zero set of C has measure zero
    have hC_null : volume {x : Fin n → ℝ | eval x C = 0} = 0 := ih C hk

    -- 4. Apply the Fubini slice lemma
    apply volume_piFinSucc_null _ (MvPolynomial.measurableSet_zeroSet p)

    -- 5. For a.e. x (outside zero set of C), the 1D slice has measure 0
    rw [ae_iff]
    apply measure_mono_null (t := {x | eval x C = 0})

    · -- 5a. Show the "bad set" ⊆ zero set of C
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      -- hx says: ¬(volume {t | Fin.cons t x ∈ zero set of p} = 0)
      -- We need: eval x C ≠ 0 leads to contradiction (so x is in zero set of C)
      by_contra hx_ne
      apply hx
      -- Since eval x C ≠ 0, the univariate polynomial q_x := q.map (eval x) is nonzero
      let q_x : Polynomial ℝ := Polynomial.map (eval x) q
      have hqx_ne : q_x ≠ 0 := by
        intro h_abs
        have : q_x.coeff k = 0 := by rw [h_abs]; simp
        simp only [q_x, Polynomial.coeff_map] at this
        exact hx_ne this
      -- By the univariate lemma, the roots of q_x have measure 0
      have h_uni := Polynomial.volume_zeroSet_eq_zero q_x hqx_ne
      -- The slice {t | Fin.cons t x ∈ zero set of p} = {t | q_x.eval t = 0}
      -- by eval_eq_eval_mv_eval': eval (Fin.cons y s) f = Polynomial.eval y (q.map (eval s))
      convert h_uni using 1
      congr 1
      ext t
      simp only [Set.mem_setOf_eq]
      rw [MvPolynomial.eval_eq_eval_mv_eval' x t p]

    · exact hC_null

end
