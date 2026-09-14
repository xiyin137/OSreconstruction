/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Init
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.SCV.TubeDomainExtension













noncomputable section

open Topology
open scoped Classical BigOperators

namespace OSReconstruction

/-- The union of one-coordinate imaginary strips for an arbitrary finite
coordinate type. -/
def fintypeFlatImaginaryUnion
    (ι : Type*) [Fintype ι] (alpha : ℝ) : Set (ι → ℝ) :=
  {t | ∃ q : ι, |t q| < alpha ∧ ∀ p : ι, p ≠ q → t p = 0}

/-- The open imaginary `l1` ball for an arbitrary finite coordinate type. -/
def fintypeImaginaryL1Domain
    (ι : Type*) [Fintype ι] (alpha : ℝ) : Set (ι → ℝ) :=
  {t | ∑ q : ι, |t q| < alpha}

theorem convex_fintypeImaginaryL1Domain
    (ι : Type*) [Fintype ι] (alpha : ℝ) :
    Convex ℝ (fintypeImaginaryL1Domain ι alpha) := by
  intro z hz w hw a b ha hb hab
  simp only [fintypeImaginaryL1Domain, Set.mem_setOf_eq] at hz hw ⊢
  have hpoint : ∀ q : ι,
      |((a • z + b • w) q)| ≤ a * |z q| + b * |w q| := by
    intro q
    calc
      |((a • z + b • w) q)|
          = |a * z q + b * w q| := by simp [Pi.smul_apply]
      _ ≤ |a * z q| + |b * w q| := abs_add_le _ _
      _ = a * |z q| + b * |w q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum_le :
      (∑ q : ι, |((a • z + b • w) q)|) ≤
        a * (∑ q : ι, |z q|) + b * (∑ q : ι, |w q|) := by
    calc
      (∑ q : ι, |((a • z + b • w) q)|)
          ≤ ∑ q : ι, (a * |z q| + b * |w q|) :=
            Finset.sum_le_sum fun q _ => hpoint q
      _ = a * (∑ q : ι, |z q|) + b * (∑ q : ι, |w q|) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
  have hlt :
      a * (∑ q : ι, |z q|) + b * (∑ q : ι, |w q|) < alpha := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hw
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by linarith
        simpa [ha1] using hz
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hzmul : a * (∑ q : ι, |z q|) < a * alpha :=
          mul_lt_mul_of_pos_left hz ha_pos
        have hwmul : b * (∑ q : ι, |w q|) < b * alpha :=
          mul_lt_mul_of_pos_left hw hb_pos
        have hcombine : a * alpha + b * alpha = alpha := by
          calc
            a * alpha + b * alpha = (a + b) * alpha := by ring
            _ = alpha := by rw [hab]; ring
        linarith
  exact lt_of_le_of_lt hsum_le hlt

theorem fintypeFlatImaginary_subset_l1Domain
    {ι : Type*} [Fintype ι] {alpha : ℝ} :
    fintypeFlatImaginaryUnion ι alpha ⊆
      fintypeImaginaryL1Domain ι alpha := by
  rintro t ⟨q, habs, hzero⟩
  have hsum : (∑ p : ι, |t p|) = |t q| := by
    refine Finset.sum_eq_single q ?_ ?_
    · intro p _ hp
      rw [hzero p hp]
      simp
    · intro hq_not
      simp at hq_not
  simpa [fintypeImaginaryL1Domain, hsum] using habs

theorem zero_mem_fintypeFlatImaginaryUnion
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {alpha : ℝ} (halpha : 0 < alpha) :
    (0 : ι → ℝ) ∈ fintypeFlatImaginaryUnion ι alpha := by
  let q : ι := Classical.choice ‹Nonempty ι›
  exact ⟨q, by simpa using halpha, by simp⟩

theorem fintypeL1Domain_subset_convexHull_flatImaginary
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {alpha : ℝ} (halpha : 0 < alpha) :
    fintypeImaginaryL1Domain ι alpha ⊆
      convexHull ℝ (fintypeFlatImaginaryUnion ι alpha) := by
  intro t ht
  let S : ℝ := ∑ q : ι, |t q|
  have hS_lt : S < alpha := by
    simpa [S, fintypeImaginaryL1Domain] using ht
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun q _ => abs_nonneg (t q)
  by_cases hS0 : S = 0
  · have ht_zero : t = 0 := by
      funext q
      have hq_abs : |t q| = 0 := by
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun p _ => abs_nonneg (t p))).1 hS0
        exact hall q (Finset.mem_univ q)
      exact abs_eq_zero.mp hq_abs
    rw [ht_zero]
    exact subset_convexHull ℝ _
      (zero_mem_fintypeFlatImaginaryUnion
        (ι := ι) (alpha := alpha) halpha)
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
    let weight : ι → ℝ := fun q => |t q| / S
    let axisPoint : ι → ι → ℝ := fun q =>
      Pi.single q (if 0 ≤ t q then S else -S)
    have hweight_nonneg :
        ∀ q ∈ (Finset.univ : Finset ι), 0 ≤ weight q := by
      intro q _
      exact div_nonneg (abs_nonneg (t q)) hS_nonneg
    have hweight_sum : (∑ q : ι, weight q) = 1 := by
      calc
        (∑ q : ι, weight q) = (∑ q : ι, |t q|) / S := by
          simp [weight, Finset.sum_div]
        _ = S / S := rfl
        _ = 1 := div_self hS_pos.ne'
    have haxis_mem :
        ∀ q ∈ (Finset.univ : Finset ι),
          axisPoint q ∈
            convexHull ℝ (fintypeFlatImaginaryUnion ι alpha) := by
      intro q _
      refine subset_convexHull ℝ _ ?_
      refine ⟨q, ?_, ?_⟩
      · have hS_abs : |(if 0 ≤ t q then S else -S)| = S := by
          by_cases htq : 0 ≤ t q
          · simp [htq, abs_of_nonneg hS_nonneg]
          · simp [htq, abs_of_nonneg hS_nonneg]
        simpa [axisPoint, hS_abs] using hS_lt
      · intro p hp
        simp [axisPoint, Pi.single_eq_of_ne hp]
    have hbary :
        (∑ q : ι, weight q • axisPoint q) ∈
          convexHull ℝ (fintypeFlatImaginaryUnion ι alpha) := by
      exact
        (convex_convexHull ℝ
          (fintypeFlatImaginaryUnion ι alpha)).sum_mem
            hweight_nonneg hweight_sum haxis_mem
    have hbary_eq : (∑ q : ι, weight q • axisPoint q) = t := by
      funext p
      have hsum_single :
          (∑ q : ι, (weight q • axisPoint q) p) =
            (weight p • axisPoint p) p := by
        refine Finset.sum_eq_single p ?_ ?_
        · intro q _ hq
          simp [axisPoint, Pi.single_eq_of_ne (Ne.symm hq)]
        · intro hp
          simp at hp
      calc
        (∑ q : ι, weight q • axisPoint q) p
            = ∑ q : ι, (weight q • axisPoint q) p := by simp
        _ = (weight p • axisPoint p) p := hsum_single
        _ = t p := by
          by_cases htp : 0 ≤ t p
          · have habs : |t p| = t p := abs_of_nonneg htp
            simp [weight, axisPoint, htp, habs, hS_pos.ne']
          · have htp_neg : t p < 0 := lt_of_not_ge htp
            have habs : |t p| = -t p := abs_of_neg htp_neg
            simp [weight, axisPoint, htp, habs, hS_pos.ne']
    simpa [hbary_eq] using hbary

/-- The convex envelope of one-coordinate imaginary strips is the open `l1`
ball for every nonempty finite coordinate type. -/
theorem convexHull_fintypeFlatImaginary_eq_l1Domain
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {alpha : ℝ} (halpha : 0 < alpha) :
    convexHull ℝ (fintypeFlatImaginaryUnion ι alpha) =
      fintypeImaginaryL1Domain ι alpha := by
  exact Set.Subset.antisymm
    (convexHull_min
      fintypeFlatImaginary_subset_l1Domain
      (convex_fintypeImaginaryL1Domain ι alpha))
    (fintypeL1Domain_subset_convexHull_flatImaginary
      (ι := ι) (alpha := alpha) halpha)

end OSReconstruction
