/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Infrastructure for multi-dimensional Edge-of-the-Wedge extension

Helper lemmas for the m ≥ 2 case of the edge-of-the-wedge theorem:
* Convex cone summation
* Linear independence in open sets
-/

open Finset

noncomputable section

/-! ### Convex cone summation -/

/-- A convex cone is closed under addition. -/
theorem convex_cone_add_mem {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {C : Set E} (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : E), 0 < t → y ∈ C → t • y ∈ C)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) : x + y ∈ C := by
  have hmid : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ C := by
    apply hconv hx hy <;> norm_num
  have heq : x + y = (2 : ℝ) • ((1/2 : ℝ) • x + (1/2 : ℝ) • y) := by
    rw [smul_add, smul_smul, smul_smul]; norm_num
  rw [heq]; exact hcone 2 _ (by norm_num) hmid

/-- In a convex cone, the sum of positive scalar multiples of elements is in the cone. -/
theorem convex_cone_sum_mem {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {C : Set E} (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : E), 0 < t → y ∈ C → t • y ∈ C)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {t : ι → ℝ} {y : ι → E}
    (ht : ∀ j ∈ s, 0 < t j) (hy : ∀ j ∈ s, y j ∈ C) :
    ∑ j ∈ s, t j • y j ∈ C := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s has ih =>
    rw [Finset.sum_cons]
    by_cases hs' : s.Nonempty
    · exact convex_cone_add_mem hconv hcone
        (hcone _ _ (ht a (mem_cons_self a s)) (hy a (mem_cons_self a s)))
        (ih hs' (fun j hj => ht j (mem_cons.mpr (Or.inr hj)))
          (fun j hj => hy j (mem_cons.mpr (Or.inr hj))))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs', sum_empty, add_zero]
      exact hcone _ _ (ht a (mem_cons_self a s)) (hy a (mem_cons_self a s))

/-- Variant over Finset.univ for Fin n. -/
theorem convex_cone_sum_univ_mem {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {C : Set E} (hconv : Convex ℝ C)
    (hcone : ∀ (t : ℝ) (y : E), 0 < t → y ∈ C → t • y ∈ C)
    {n : ℕ} (hn : 0 < n)
    {t : Fin n → ℝ} {y : Fin n → E}
    (ht : ∀ j, 0 < t j) (hy : ∀ j, y j ∈ C) :
    ∑ j : Fin n, t j • y j ∈ C := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact convex_cone_sum_mem hconv hcone Finset.univ_nonempty
    (fun j _ => ht j) (fun j _ => hy j)

/-! ### Linear independence in open sets -/

/-- Standard basis vector in Fin m → ℝ. Defined as Pi.single. -/
private def stdBasis (m : ℕ) (k : Fin m) : Fin m → ℝ :=
  fun j => if j = k then 1 else 0

private theorem stdBasis_eq_single {m : ℕ} (k : Fin m) :
    stdBasis m k = Pi.single k 1 := by
  ext j; simp [stdBasis, Pi.single_apply]

private theorem stdBasis_norm {m : ℕ} (k : Fin m) : ‖stdBasis m k‖ = 1 := by
  rw [stdBasis_eq_single, Pi.norm_single, norm_one]

/-- Vectors y₀ + ε · eₖ are linearly independent for suitable ε > 0.
The degenerate case ε + ∑ y₀ i = 0 is avoided by choosing between ρ/2 and ρ/3. -/
lemma open_ball_contains_linIndep {m : ℕ} (_hm : 0 < m)
    (y₀ : Fin m → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧
      LinearIndependent ℝ (fun k : Fin m => y₀ + ε • stdBasis m k) := by
  set S := ∑ i : Fin m, y₀ i
  -- Find ε with ε + S ≠ 0
  have hε_exists : ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧ ε + S ≠ 0 := by
    by_cases h1 : ρ / 2 + S ≠ 0
    · exact ⟨ρ / 2, by positivity, by linarith, h1⟩
    · push_neg at h1
      exact ⟨ρ / 3, by positivity, by linarith, by intro h2; linarith⟩
  obtain ⟨ε, hε_pos, hε_lt, hεS⟩ := hε_exists
  refine ⟨ε, hε_pos, hε_lt, ?_⟩
  -- Use Fintype.linearIndependent_iff for a cleaner proof
  rw [Fintype.linearIndependent_iff]
  intro c hsc
  -- hsc : ∑ k, c k • (y₀ + ε • stdBasis m k) = 0
  -- Component i: (∑ c_k) * y₀ i + ε * c i = 0
  have hcomp : ∀ i : Fin m, (∑ k, c k) * y₀ i + ε * c i = 0 := by
    intro i
    have := congr_fun hsc i
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Pi.add_apply, stdBasis] at this
    -- this : ∑ k, c k * (y₀ i + ε * if i = k then 1 else 0) = 0
    simp only [mul_add, sum_add_distrib, ← sum_mul, mul_ite, mul_one, mul_zero] at this
    -- this : (∑ k, c k) * y₀ i + ∑ k, if i = k then c k * ε else 0 = 0
    rwa [sum_ite_eq, if_pos (mem_univ i), mul_comm (c i) ε] at this
  -- Main argument
  intro k
  by_cases hSc : ∑ j, c j = 0
  · -- ∑ c_j = 0 → ε * c_k = 0 → c_k = 0
    have := hcomp k; rw [hSc, zero_mul, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hε_pos)
  · -- ∑ c_j ≠ 0 → contradiction via (∑ c_j) * (ε + S) = 0
    exfalso
    have hc_eq : ∀ i, ε * c i = -(∑ j, c j) * y₀ i := by
      intro i; linarith [hcomp i]
    -- Sum: ε * (∑ c_i) = -(∑ c_j) * S
    have hsum : ε * ∑ i, c i = -(∑ j, c j) * S := by
      rw [mul_sum]; simp_rw [hc_eq]; rw [← mul_sum]
    -- (∑ c_j) * (ε + S) = 0
    have : (∑ j, c j) * (ε + S) = 0 := by nlinarith
    exact hεS ((mul_eq_zero.mp this).resolve_left hSc)

/-- An open set in ℝᵐ (m ≥ 1) contains m linearly independent vectors. -/
theorem open_set_contains_basis {m : ℕ} (hm : 0 < m)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (ys : Fin m → (Fin m → ℝ)),
      (∀ k, ys k ∈ U) ∧ LinearIndependent ℝ ys := by
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  obtain ⟨ε, hε_pos, hε_lt, hli⟩ := open_ball_contains_linIndep hm y₀ ρ hρ
  refine ⟨fun k => y₀ + ε • stdBasis m k, ?_, hli⟩
  intro k; apply hball
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show y₀ + ε • stdBasis m k - y₀ = ε • stdBasis m k from by abel]
  rw [norm_smul, Real.norm_of_nonneg hε_pos.le, stdBasis_norm, mul_one]
  exact hε_lt

end
