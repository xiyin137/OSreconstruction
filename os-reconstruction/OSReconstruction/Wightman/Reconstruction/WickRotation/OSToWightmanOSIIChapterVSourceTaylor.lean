/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVScalarTaylor



















noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Multi-index positive-time source coefficients evaluated at one complex
increment. -/
structure PositiveTimeSourceCoefficientData
    (d n k : ℕ) [NeZero d] where
  coefficient :
    (Fin k → ℕ) → euclideanPositiveTimeSubmodule (d := d) n
  increment : Fin k → ℂ

namespace PositiveTimeSourceCoefficientData

/-- The source Taylor monomial attached to one multi-index. -/
def monomial
    {d n k : ℕ} [NeZero d]
    (D : PositiveTimeSourceCoefficientData d n k)
    (α : Fin k → ℕ) : ℂ :=
  ∏ i, D.increment i ^ α i

/-- The positive-time source Taylor polynomial homogeneous of total degree
`p`. -/
def homogeneousSource
    {d n k : ℕ} [NeZero d]
    (D : PositiveTimeSourceCoefficientData d n k)
    (p : ℕ) : euclideanPositiveTimeSubmodule (d := d) n :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
    D.monomial α • D.coefficient α

/-- The unweighted reflected Schwinger Gram coefficient of two source
multi-indices. -/
def scalarGram
    {d n k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (D : PositiveTimeSourceCoefficientData d n k)
    (α β : Fin k → ℕ) : ℂ :=
  OS.S (n + n)
    (ZeroDiagonalSchwartz.ofClassical
      ((D.coefficient α).1.osConjTensorProduct (D.coefficient β).1))

end PositiveTimeSourceCoefficientData

/-- Termwise compatibility obtained by differentiating the reflected scalar
pairing identity at a positive real basepoint.

The third field is the genuine OS-II `(5.17)` derivative identity.  The first
two fields only identify the independent reflected-left/right scalar
increments with the single source increment. -/
structure ReflectedSourceCauchyCompatibility
    {d n k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (S : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k) : Prop where
  left_increment :
    ∀ i, D.increment (Fin.castAdd k i) =
      starRingEnd ℂ (S.increment i)
  right_increment :
    ∀ i, D.increment (Fin.natAdd k i) = S.increment i
  cauchyCoeff_eq_scalarGram :
    ∀ α β,
      SCV.cauchyCoeffPolydisc D.scalar D.center
          (fun _ => D.radius) (Fin.append α β) =
        S.scalarGram OS α β

namespace PositiveTimeSourceCoefficientData

/-- Reflection positivity and source linearity expand a homogeneous source
Gram coefficient into its exact finite multi-index double sum. -/
theorem positiveTimeTaylorScalarGram_homogeneousSource
    {d n k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (D : PositiveTimeSourceCoefficientData d n k)
    (p q : ℕ) :
    positiveTimeTaylorScalarGram OS n D.homogeneousSource p q =
      ∑ α ∈ Finset.Nat.antidiagonalTuple k p,
        ∑ β ∈ Finset.Nat.antidiagonalTuple k q,
          starRingEnd ℂ (D.monomial α) * D.monomial β *
            D.scalarGram OS α β := by
  rw [positiveTimeTaylorScalarGram,
    ← osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger
      OS n n (D.homogeneousSource p) (D.homogeneousSource q)]
  simp only [homogeneousSource, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  rw [osiiPositiveTimeSingleVectorCLM_inner_eq_schwinger]
  simp only [scalarGram]
  ring

/-- Termwise reflected Cauchy compatibility identifies each weighted scalar
multi-index term with the corresponding weighted source Gram coefficient. -/
theorem reflectedCauchy_multiIndexTerm_append_eq
    {d n k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (S : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k)
    (C : ReflectedSourceCauchyCompatibility OS S D)
    (α β : Fin k → ℕ) :
    D.multiIndexTerm (Fin.append α β) =
      starRingEnd ℂ (S.monomial α) * S.monomial β *
        S.scalarGram OS α β := by
  simp only [ReflectedCauchyCoefficientData.multiIndexTerm,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    C.left_increment, C.right_increment, C.cauchyCoeff_eq_scalarGram,
    monomial, map_prod, map_pow]

/-- The grouped reflected Gram identity follows from the termwise
`(5.17)` compatibility; it is not an additional analytic assumption. -/
theorem positiveTimeTaylorScalarGram_homogeneousSource_eq_cauchyScalarGram
    {d n k : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (S : PositiveTimeSourceCoefficientData d n k)
    (D : ReflectedCauchyCoefficientData k)
    (C : ReflectedSourceCauchyCompatibility OS S D)
    (p q : ℕ) :
    positiveTimeTaylorScalarGram OS n S.homogeneousSource p q =
      D.scalarGram p q := by
  rw [S.positiveTimeTaylorScalarGram_homogeneousSource OS p q,
    D.scalarGram_eq_sum_antidiagonalTuple p q]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  exact (S.reflectedCauchy_multiIndexTerm_append_eq OS D C α β).symm

end PositiveTimeSourceCoefficientData
end OSIIChapterV
end OSReconstruction
