/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

/-!
# Sinusoid Separation Lemma

For finitely many points in ℝ² whose projections are positive for at least one angle,
the linear projections L_k(b) = A_k cos b + B_k sin b can be made simultaneously
distinct while staying positive, for some angle b.

This is the key lemma for proving that a.e. Euclidean configuration lies in the
permuted extended tube (W11 in the OS reconstruction).

## Main result

`exists_angle_all_pos_and_distinct` — assuming there is already one angle where all
projections are positive, there exists b such that all L_k(b) are still positive and
pairwise distinct.
-/

noncomputable section

open Real

/-- Two distinct sinusoids can agree only on a set with empty interior. -/
private lemma sinusoid_eq_interior_eq_empty {A₁ B₁ A₂ B₂ : ℝ}
    (h : (A₁, B₁) ≠ (A₂, B₂)) :
    interior {b : ℝ | A₁ * cos b + B₁ * sin b = A₂ * cos b + B₂ * sin b} = ∅ := by
  let S : Set ℝ := {b : ℝ | A₁ * cos b + B₁ * sin b = A₂ * cos b + B₂ * sin b}
  let dA : ℝ := A₁ - A₂
  let dB : ℝ := B₁ - B₂
  have hd : (dA, dB) ≠ (0, 0) := by
    intro hzero
    apply h
    rw [Prod.mk.injEq] at hzero
    rw [Prod.mk.injEq]
    exact ⟨sub_eq_zero.mp hzero.1, sub_eq_zero.mp hzero.2⟩
  by_contra hS
  obtain ⟨x, hx⟩ : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let δ : ℝ := min (ε / 2) (π / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    rw [lt_min_iff]
    constructor
    · exact half_pos hε
    · nlinarith [Real.pi_pos]
  have hδltε : δ < ε := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδltpi : δ < π := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by nlinarith [Real.pi_pos])
  have hδsin_ne : sin δ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hδpos hδltpi)
  have hyBall : x + δ ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    ring_nf
    rw [abs_of_nonneg (le_of_lt hδpos)]
    exact hδltε
  have hxS : x ∈ S := interior_subset hx
  have hyS : x + δ ∈ S := interior_subset (hball hyBall)
  have hx0 : dA * cos x + dB * sin x = 0 := by
    dsimp [S, dA, dB] at hxS
    linarith
  have hy0 : dA * cos (x + δ) + dB * sin (x + δ) = 0 := by
    dsimp [S, dA, dB] at hyS
    linarith
  have hdA_mul : dA * sin δ = 0 := by
    have h1 := congrArg (fun t => t * sin (x + δ)) hx0
    have h2 := congrArg (fun t => t * sin x) hy0
    simp only [zero_mul] at h1 h2
    rw [Real.sin_add] at h1
    rw [Real.cos_add, Real.sin_add] at h2
    ring_nf at h1 h2
    nlinarith [h1, h2, Real.cos_sq_add_sin_sq x]
  have hdB_mul : dB * sin δ = 0 := by
    have h1 := congrArg (fun t => t * cos (x + δ)) hx0
    have h2 := congrArg (fun t => t * cos x) hy0
    simp only [zero_mul] at h1 h2
    rw [Real.cos_add] at h1
    rw [Real.cos_add, Real.sin_add] at h2
    ring_nf at h1 h2
    nlinarith [h1, h2, Real.cos_sq_add_sin_sq x]
  have hdA0 : dA = 0 := by
    rcases mul_eq_zero.mp hdA_mul with hzero | hzero
    · exact hzero
    · exact False.elim (hδsin_ne hzero)
  have hdB0 : dB = 0 := by
    rcases mul_eq_zero.mp hdB_mul with hzero | hzero
    · exact hzero
    · exact False.elim (hδsin_ne hzero)
  exact hd (by rw [hdA0, hdB0])

/-- A nonzero sinusoid has a zero set with empty interior. -/
private lemma sinusoid_zero_interior_eq_empty {A B : ℝ} (h : (A, B) ≠ (0, 0)) :
    interior {b : ℝ | A * cos b + B * sin b = 0} = ∅ := by
  simpa using
    (sinusoid_eq_interior_eq_empty (A₁ := A) (B₁ := B) (A₂ := 0) (B₂ := 0) h)

/-- **Sinusoid separation lemma.**

For n ≥ 1 pairwise distinct nonzero points (A_k, B_k) in ℝ², assume there is at
least one angle `b₀` at which all projections are already strictly positive.
Then there exists an angle b ∈ ℝ such that the linear projections
L_k(b) = A_k · cos(b) + B_k · sin(b) are all distinct and strictly positive.

Proof sketch: the positivity hypothesis gives an open interval on which all
projections stay positive. For each `i ≠ j`, the coincidence set
`{b | L_i(b) = L_j(b)}` has empty interior, and similarly each zero set
`{b | L_i(b) = 0}` has empty interior. A finite union of such bad sets still
has empty interior, so it cannot cover the whole positive interval. -/
theorem exists_angle_all_pos_and_distinct {n : ℕ} (_hn : 0 < n)
    (A B : Fin n → ℝ)
    (hdistinct : ∀ i j : Fin n, i ≠ j → (A i, B i) ≠ (A j, B j))
    (_hnonzero : ∀ i : Fin n, (A i, B i) ≠ (0, 0))
    (hpositive : ∃ b₀ : ℝ, ∀ i : Fin n, 0 < A i * cos b₀ + B i * sin b₀) :
    ∃ b : ℝ,
      (∀ i j : Fin n, i ≠ j →
        A i * cos b + B i * sin b ≠ A j * cos b + B j * sin b) ∧
      (∀ i : Fin n, 0 < A i * cos b + B i * sin b) := by
  -- Step 1: The "good" set U = {b | ∀ i, L_i(b) > 0} is open and nonempty.
  obtain ⟨b₀, hb₀⟩ := hpositive
  let U := {b : ℝ | ∀ i : Fin n, 0 < A i * cos b + B i * sin b}
  have hU_open : IsOpen U := by
    rw [show U = ⋂ i : Fin n, {b : ℝ | 0 < A i * cos b + B i * sin b} by
      ext b
      simp [U]]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const
      ((continuous_const.mul Real.continuous_cos).add
       (continuous_const.mul Real.continuous_sin))
  have hb₀_mem : b₀ ∈ U := hb₀
  -- Step 2: The "bad" set B = ⋃_{i≠j} {b | L_i = L_j} has empty interior.
  let S : {p : Fin n × Fin n // p.1 ≠ p.2} → Set ℝ := fun p =>
    {b : ℝ | A p.1.1 * cos b + B p.1.1 * sin b = A p.1.2 * cos b + B p.1.2 * sin b}
  let B := ⋃ p, S p
  have hB_interior : interior B = ∅ := by
    have hS_closed : ∀ p, IsClosed (S p) := by
      intro p
      exact isClosed_eq
        ((continuous_const.mul Real.continuous_cos).add
          (continuous_const.mul Real.continuous_sin))
        ((continuous_const.mul Real.continuous_cos).add
          (continuous_const.mul Real.continuous_sin))
    have hS_interior : ∀ p, interior (S p) = ∅ := by
      intro p
      exact sinusoid_eq_interior_eq_empty (hdistinct p.1.1 p.1.2 p.2)
    let t : Finset {p : Fin n × Fin n // p.1 ≠ p.2} := Finset.univ
    have hfinite :
        ∀ s : Finset {p : Fin n × Fin n // p.1 ≠ p.2}, interior (⋃ p ∈ s, S p) = ∅ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha hs =>
          rw [show (⋃ p ∈ insert a s, S p) = S a ∪ ⋃ p ∈ s, S p by
            simp]
          rw [interior_union_isClosed_of_interior_empty (hS_closed a) hs]
          exact hS_interior a
    simpa [B, S, t] using hfinite t
  -- Step 3: U is not contained in B (open nonempty set vs empty interior).
  -- So U \ B is nonempty.
  have hU_not_sub_B : ¬ (U ⊆ B) := by
    intro hsub
    have hb₀_int : b₀ ∈ interior B := interior_maximal hsub hU_open hb₀_mem
    simp [hB_interior] at hb₀_int
  obtain ⟨b, hbU, hbB⟩ := Set.not_subset.mp hU_not_sub_B
  refine ⟨b, ?_, hbU⟩
  intro i j hij hEq
  apply hbB
  simpa [B, S] using
    (Set.mem_iUnion.mpr
      ⟨⟨(i, j), hij⟩, hEq⟩ :
        b ∈ ⋃ p : {p : Fin n × Fin n // p.1 ≠ p.2}, S p)

end
