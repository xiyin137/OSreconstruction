import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The tested Taylor endpoint formula

The boundary argument uses Taylor's formula only after spatial and time
testing. The remainder is weighted at the singular endpoint, so a bound of
order `s^(-M)` is integrable after multiplication by `s^M`.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval

namespace OSReconstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

private def testedTaylorPolynomial
    (J : Nat -> Real -> E) (M : Nat) (s : Real) : E :=
  ∑ j ∈ Finset.range (M + 1),
    ((j.factorial : Real)⁻¹ * (-s) ^ j) • J j s

private theorem hasDerivAt_testedTaylorCoefficient
    (j : Nat) (s : Real) :
    HasDerivAt
      (fun u : Real => ((j + 1).factorial : Real)⁻¹ * (-u) ^ (j + 1))
      (-((j.factorial : Real)⁻¹ * (-s) ^ j)) s := by
  convert (monomial_has_deriv_aux s 0 j).const_mul
    (((j + 1).factorial : Real)⁻¹) using 1
  · simp
  · simp only [zero_sub, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field

private theorem hasDerivAt_testedTaylorPolynomial
    (J : Nat -> Real -> E) (M : Nat) (s : Real)
    (hJ : forall j, HasDerivAt (J j) (J (j + 1) s) s) :
    HasDerivAt (testedTaylorPolynomial J M)
      (((M.factorial : Real)⁻¹ * (-s) ^ M) • J (M + 1) s) s := by
  induction M with
  | zero =>
    have hfun : testedTaylorPolynomial J 0 = J 0 := by
      funext u
      simp [testedTaylorPolynomial]
    rw [hfun]
    simpa using hJ 0
  | succ M ih =>
    have hterm := (hasDerivAt_testedTaylorCoefficient M s).smul (hJ (M + 1))
    have hfun : testedTaylorPolynomial J (M + 1) =
        fun u => testedTaylorPolynomial J M u +
          (((M + 1).factorial : Real)⁻¹ * (-u) ^ (M + 1)) • J (M + 1) u := by
      funext u
      exact Finset.sum_range_succ _ (M + 1)
    rw [hfun]
    convert ih.add hterm using 1
    module

/-- Taylor expansion at the regular endpoint `1`, evaluated at `0`.
The remainder vanishes to order `M` at the endpoint that will become
singular in the tube-boundary limit. -/
theorem osii_testedTaylor_endpoint [CompleteSpace E]
    (J : Nat -> Real -> E) (M : Nat)
    (hJ : forall j s, s ∈ Icc (0 : Real) 1 ->
      HasDerivAt (J j) (J (j + 1) s) s) :
    J 0 0 =
      (∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (-1) ^ j) • J j 1) -
      (M.factorial : Real)⁻¹ •
        ∫ s in (0 : Real)..1, (-s) ^ M • J (M + 1) s := by
  have hderiv : forall s, s ∈ uIcc (0 : Real) 1 ->
      HasDerivAt (testedTaylorPolynomial J M)
        (((M.factorial : Real)⁻¹ * (-s) ^ M) • J (M + 1) s) s := by
    intro s hs
    exact hasDerivAt_testedTaylorPolynomial J M s
      (fun j => hJ j s (by simpa using hs))
  have hcont : ContinuousOn (J (M + 1)) (uIcc (0 : Real) 1) := by
    intro s hs
    exact (hJ (M + 1) s (by simpa using hs)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun s : Real => ((M.factorial : Real)⁻¹ * (-s) ^ M) • J (M + 1) s)
      volume 0 1 :=
    ((continuousOn_const.mul (continuousOn_id.neg.pow M)).smul hcont
      ).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hzero : testedTaylorPolynomial J M 0 = J 0 0 := by
    simp [testedTaylorPolynomial, Finset.sum_range_succ']
  have hone : testedTaylorPolynomial J M 1 =
      ∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (-1) ^ j) • J j 1 := rfl
  simp_rw [mul_smul] at hftc
  rw [intervalIntegral.integral_smul, hzero, hone] at hftc
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (eq_sub_iff_add_eq.mp hftc)

/-- The same tested expansion on an arbitrary regular interval. The target
endpoint `a` is kept inside the remainder kernel. -/
theorem osii_testedTaylor_between [CompleteSpace E]
    (J : Nat -> Real -> E) (M : Nat) (a b : Real)
    (hJ : forall j s, s ∈ uIcc a b -> HasDerivAt (J j) (J (j + 1) s) s) :
    J 0 a =
      (∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (a - b) ^ j) • J j b) -
      (M.factorial : Real)⁻¹ •
        ∫ s in a..b, (a - s) ^ M • J (M + 1) s := by
  let K : Nat -> Real -> E := fun j t => J j (t + a)
  have hderiv : forall s, s ∈ uIcc a b ->
      HasDerivAt (fun t => testedTaylorPolynomial K M (t - a))
        (((M.factorial : Real)⁻¹ * (a - s) ^ M) • J (M + 1) s) s := by
    intro s hs
    have hK : forall j, HasDerivAt (K j) (K (j + 1) (s - a)) (s - a) := by
      intro j
      have h : HasDerivAt (J j) (J (j + 1) s) (s - a + a) := by
        simpa only [sub_add_cancel] using hJ j s hs
      simpa only [K, sub_add_cancel] using h.comp_add_const (s - a) a
    have h := (hasDerivAt_testedTaylorPolynomial K M (s - a) hK).comp_sub_const s a
    simpa only [K, sub_add_cancel, neg_sub] using h
  have hcont : ContinuousOn (J (M + 1)) (uIcc a b) := by
    intro s hs
    exact (hJ (M + 1) s hs).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun s : Real => ((M.factorial : Real)⁻¹ * (a - s) ^ M) • J (M + 1) s)
      volume a b :=
    ((continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow M)).smul
      hcont).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have ha : testedTaylorPolynomial K M (a - a) = J 0 a := by
    simp [testedTaylorPolynomial, K, Finset.sum_range_succ']
  have hb : testedTaylorPolynomial K M (b - a) =
      ∑ j ∈ Finset.range (M + 1),
        ((j.factorial : Real)⁻¹ * (a - b) ^ j) • J j b := by
    simp only [testedTaylorPolynomial, K, sub_add_cancel, neg_sub]
  simp_rw [mul_smul] at hftc
  rw [intervalIntegral.integral_smul, ha, hb] at hftc
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (eq_sub_iff_add_eq.mp hftc)

end OSReconstruction
