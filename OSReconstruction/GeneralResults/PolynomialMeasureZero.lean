/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Zero Sets of Real Polynomials Have Lebesgue Measure Zero

The zero set of a nonzero multivariate polynomial p ∈ ℝ[x₁,...,xₙ] has
Lebesgue measure zero in ℝⁿ. This is a fundamental result in real algebraic
geometry, used in QFT to show that "generic" configurations avoid algebraic
degeneracies (e.g., coincident times, lightlike separations).

## Main result

- `MvPolynomial.volume_zeroSet_eq_zero` — (axiom) the zero set of a nonzero
  polynomial has Lebesgue measure zero

## Mathematical content

**Theorem.** Let p ∈ ℝ[x₁,...,xₙ] be a nonzero polynomial. Then

  λⁿ({x ∈ ℝⁿ | p(x) = 0}) = 0

where λⁿ is the n-dimensional Lebesgue measure.

**Proof sketch** (induction on n):

1. **Base case (n = 1):** A nonzero univariate polynomial of degree d has at
   most d roots. A finite set has Lebesgue measure zero.

2. **Inductive step (n → n+1):** Write p(x₁,...,xₙ,xₙ₊₁) as a polynomial
   in xₙ₊₁ with coefficients in ℝ[x₁,...,xₙ]:

     p = Σᵢ aᵢ(x₁,...,xₙ) · xₙ₊₁ⁱ

   Since p ≠ 0, at least one coefficient aⱼ is nonzero. By the induction
   hypothesis, λⁿ({x | aⱼ(x) = 0}) = 0. For a.e. (x₁,...,xₙ) (outside
   this null set), the univariate polynomial p(x₁,...,xₙ, ·) is nonzero,
   hence has at most finitely many roots. By Fubini-Tonelli:

     λⁿ⁺¹({(x,t) | p(x,t) = 0}) = ∫ λ¹({t | p(x,t) = 0}) dλⁿ(x) = 0

   since the inner measure is zero for a.e. x.

## Application to QFT

In the OS reconstruction theorem, this result is used to show that for a.e.
Euclidean spacetime configuration (x₁,...,xₙ), the Wick-rotated configuration
lies in the permuted extended tube (PET). The configurations NOT in PET are
contained in algebraic varieties defined by:
- coincident time conditions: xᵢ(0) = xⱼ(0)
- lightlike separation conditions: (xᵢ - xⱼ)² = 0 (Minkowski norm)

Both are zero sets of nonzero polynomials, hence have measure zero.

## References

- Caron-Traynor, "The zero set of a polynomial" (1971)
- Okamoto, "Distinctness of the eigenvalues of a quadratic form in a
  multicanonical variable" (1973)
- Mityagin, "The zero set of a real analytic function" (2015), §1
  (survey of the polynomial case with references to classical literature)
- Bochnak-Coste-Roy, "Real Algebraic Geometry", Proposition 2.8.2
-/

import OSReconstruction.GeneralResults.PolynomialMeasureZeroProof

noncomputable section

open MeasureTheory MvPolynomial

/-! ## Main axiom -/

/-- **The zero set of a nonzero multivariate polynomial has Lebesgue measure zero.**

For `p ∈ ℝ[x₁,...,xₙ]` with `p ≠ 0`:

  `volume {x : Fin n → ℝ | eval x p = 0} = 0`

This is proved by induction on `n`:
- `n = 1`: nonzero polynomial has finitely many roots
- `n + 1`: Fubini + IH on the leading coefficient's zero set

The result extends to countable unions: a countable union of proper algebraic
varieties in ℝⁿ has Lebesgue measure zero (by `measure_iUnion_null`).

This is a standard result in real algebraic geometry. It is not yet in
Mathlib (as of 2026-03) and would be a natural contribution.

**Downstream use:** `wickRotation_not_in_PET_null` in
`ForwardTubeLorentz.lean` — a.e. Wick-rotated Euclidean configuration
lies in the permuted extended tube. -/
theorem MvPolynomial.volume_zeroSet_eq_zero
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | eval x p = 0} = 0 :=
  MvPolynomial.volume_zeroSet_eq_zero_proved n p hp

/-! ## Corollaries -/

/-- **Countable union of polynomial zero sets has measure zero.** -/
theorem MvPolynomial.volume_countableUnion_zeroSet_eq_zero
    (n : ℕ) {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin n) ℝ) (hp : ∀ i, p i ≠ 0) :
    volume (⋃ i, {x : Fin n → ℝ | eval x (p i) = 0}) = 0 :=
  measure_iUnion_null fun i ↦ volume_zeroSet_eq_zero n (p i) (hp i)

/-- **The complement of a polynomial zero set has full measure.** -/
theorem MvPolynomial.ae_ne_zero
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∀ᵐ x : Fin n → ℝ ∂volume, eval x p ≠ 0 := by
  rw [ae_iff]
  simpa using volume_zeroSet_eq_zero n p hp
