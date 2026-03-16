/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Universal Projection Lemma (Ruelle's Lemma)

For any n points in ℝ^{d+1} (d ≥ 1), there exists a universal constant c > 0
and a proper rotation R ∈ SO(d+1) such that the time-axis projections of ALL
pairwise differences are bounded below by c times their full Euclidean distance.

## Proof Strategy (Polynomial Root Counting + Compactness)

1. **Moment curve**: For t ∈ ℝ, define p(t) = (1, t, t², ..., t^d) ∈ ℝ^{d+1}.
   For any unit vector u, ⟨p(t), u⟩ is a nonzero polynomial of degree ≤ d,
   so it has at most d roots.

2. **Pigeonhole**: With K = n(n-1)/2 pairs, the total number of "bad" values
   of t (where some pair is orthogonal to p(t)) is at most K·d. Choose
   M = K·d + 1 candidate values; at least one works for all pairs.

3. **Compactness**: The function g(U) = max_v min_{pairs} |⟨v, U_ij⟩| over
   a finite set V of normalized candidate directions is continuous on the
   compact space (S^d)^K. Since g > 0 everywhere, its minimum c > 0.

4. **Construct R**: Extend the winning direction v to an orthonormal basis
   via Gram-Schmidt, forming R ∈ SO(d+1) with v as its first row.

## References

* Ruelle, "Statistical Mechanics", §3
* Glimm-Jaffe, "Quantum Physics", Ch. 6
-/

open scoped Classical
noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Step 1: Moment curve and polynomial non-vanishing -/

/-- The moment curve: p(t) = (1, t, t², ..., t^d) in ℝ^{d+1}. -/
def momentCurve (d : ℕ) (t : ℝ) : Fin (d + 1) → ℝ :=
  fun i => t ^ (i : ℕ)

/-- The moment curve is never zero because its first coordinate is `1`. -/
theorem momentCurve_ne_zero (d : ℕ) (t : ℝ) : momentCurve d t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [momentCurve] at h0

/-- The normalized moment-curve direction. -/
def normalizedMomentCurve (d : ℕ) (t : ℝ) : Fin (d + 1) → ℝ :=
  ‖momentCurve d t‖⁻¹ • momentCurve d t

/-- The normalized moment curve has norm `1`. -/
theorem norm_normalizedMomentCurve (d : ℕ) (t : ℝ) :
    ‖normalizedMomentCurve d t‖ = 1 := by
  unfold normalizedMomentCurve
  have hmc : ‖momentCurve d t‖ ≠ 0 := norm_ne_zero_iff.mpr (momentCurve_ne_zero d t)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  field_simp [hmc]

/-- The dot product ⟨p(t), u⟩ as a polynomial in t.
    This is u₀ + u₁·t + u₂·t² + ... + u_d·t^d. -/
def momentPoly (d : ℕ) (u : Fin (d + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (d + 1), Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)

/-- The moment polynomial evaluated at t equals the dot product ⟨p(t), u⟩. -/
theorem momentPoly_eval (u : Fin (d + 1) → ℝ) (t : ℝ) :
    (momentPoly d u).eval t = ∑ i : Fin (d + 1), u i * t ^ (i : ℕ) := by
  simp [momentPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- If u ≠ 0, then momentPoly d u is a nonzero polynomial. -/
theorem momentPoly_ne_zero (u : Fin (d + 1) → ℝ) (hu : u ≠ 0) :
    momentPoly d u ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hzero
    apply hu
    ext j
    by_contra hj
    exact hzero ⟨j, hj⟩
  have hcoeff : (momentPoly d u).coeff (i : ℕ) = u i := by
    calc
      (momentPoly d u).coeff (i : ℕ)
        = ∑ j : Fin (d + 1), if (i : ℕ) = (j : ℕ) then u j else 0 := by
            simp [momentPoly, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      _ = ∑ j : Fin (d + 1), if i = j then u j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i = j
            · simp [hij]
            · have hij' : (i : ℕ) ≠ (j : ℕ) := (Fin.ne_iff_vne i j).mp hij
              simp [hij, hij']
      _ = u i := by
            simpa using (Finset.sum_ite_eq Finset.univ i u)
  have : (momentPoly d u).coeff (i : ℕ) = 0 := by simpa [h]
  exact hi (hcoeff.symm.trans this)

/-- A nonzero polynomial of degree ≤ d has at most d roots. -/
theorem momentPoly_roots_finite (u : Fin (d + 1) → ℝ) (hu : u ≠ 0) :
    ((momentPoly d u).roots.toFinset).card ≤ d := by
  have hdeg : (momentPoly d u).natDegree ≤ d := by
    unfold momentPoly
    calc
      (∑ i : Fin (d + 1), Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)).natDegree
        ≤ Finset.univ.fold max 0
            (fun i : Fin (d + 1) => (Polynomial.C (u i) * Polynomial.X ^ (i : ℕ)).natDegree) := by
              exact Polynomial.natDegree_sum_le Finset.univ _
      _ ≤ d := by
        rw [Finset.fold_max_le]
        constructor
        · omega
        · intro i hi
          exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (u i) (i : ℕ))
            (Nat.lt_succ_iff.mp i.2)
  calc
    ((momentPoly d u).roots.toFinset).card ≤ (momentPoly d u).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (momentPoly d u).natDegree := Polynomial.card_roots' (momentPoly d u)
    _ ≤ d := hdeg

/-- For any finite collection of unit vectors, there exists t such that
    p(t) is not orthogonal to any of them. -/
theorem exists_nonorthogonal_moment
    (S : Finset (Fin (d + 1) → ℝ)) (hS : ∀ u ∈ S, u ≠ 0) :
    ∃ t : ℝ, ∀ u ∈ S, ∑ i : Fin (d + 1), u i * t ^ (i : ℕ) ≠ 0 := by
  let badSet : Finset ℝ := S.biUnion fun u => (momentPoly d u).roots.toFinset
  obtain ⟨t, ht⟩ := Finset.exists_notMem badSet
  refine ⟨t, ?_⟩
  intro u hu hEval
  have hu0 : momentPoly d u ≠ 0 := momentPoly_ne_zero (d := d) u (hS u hu)
  have hroot : t ∈ (momentPoly d u).roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    rw [Polynomial.mem_roots hu0]
    rw [Polynomial.IsRoot, momentPoly_eval]
    exact hEval
  exact ht (Finset.mem_biUnion.mpr ⟨u, hu, hroot⟩)

/-- A quantitative version of `exists_nonorthogonal_moment` using only finitely
    many candidate parameters. -/
theorem exists_nonorthogonal_moment_in_candidates
    (S : Finset (Fin (d + 1) → ℝ)) (hS : ∀ u ∈ S, u ≠ 0) :
    ∃ t ∈ (Finset.range (S.card * d + 1)).image (fun m : ℕ => (m : ℝ)),
      ∀ u ∈ S, ∑ i : Fin (d + 1), u i * t ^ (i : ℕ) ≠ 0 := by
  let badSet : Finset ℝ := S.biUnion fun u => (momentPoly d u).roots.toFinset
  have hbad_card : badSet.card ≤ S.card * d := by
    calc
      badSet.card ≤ ∑ u ∈ S, ((momentPoly d u).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ S, d := by
        apply Finset.sum_le_sum
        intro u hu
        exact momentPoly_roots_finite (d := d) u (hS u hu)
      _ = S.card * d := by simp
  let candidates : Finset ℝ := (Finset.range (S.card * d + 1)).image (fun m : ℕ => (m : ℝ))
  have hcand_card : candidates.card = S.card * d + 1 := by
    dsimp [candidates]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hlt : badSet.card < candidates.card := by
    rw [hcand_card]
    omega
  obtain ⟨t, ht_mem, ht_not_mem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨t, ht_mem, ?_⟩
  intro u hu hEval
  have hu0 : momentPoly d u ≠ 0 := momentPoly_ne_zero (d := d) u (hS u hu)
  have hroot : t ∈ (momentPoly d u).roots.toFinset := by
    apply Multiset.mem_toFinset.mpr
    rw [Polynomial.mem_roots hu0]
    rw [Polynomial.IsRoot, momentPoly_eval]
    exact hEval
  exact ht_not_mem (Finset.mem_biUnion.mpr ⟨u, hu, hroot⟩)

/-! ### Step 2: Finite candidate set and compactness -/

/-- A finite set of candidate moment-curve parameters large enough for the
    pigeonhole argument. -/
def universalProjectionCandidates (n d : ℕ) : Finset ℝ :=
  (Finset.range (n * n * d + 1)).image (fun m : ℕ => (m : ℝ))

/-- The absolute projection against a moment-curve direction. -/
def momentProjection (d : ℕ) (t : ℝ) (u : Fin (d + 1) → ℝ) : ℝ :=
  |∑ i : Fin (d + 1), normalizedMomentCurve d t i * u i|

/-- A pointwise bound on the moment projection for vectors of sup norm `1`. -/
theorem momentProjection_le_dim (t : ℝ) (u : Fin (d + 1) → ℝ) (hu : ‖u‖ = 1) :
    momentProjection d t u ≤ d + 1 := by
  unfold momentProjection
  calc
    |∑ i : Fin (d + 1), normalizedMomentCurve d t i * u i|
      ≤ ∑ i : Fin (d + 1), |normalizedMomentCurve d t i * u i| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (d + 1), |normalizedMomentCurve d t i| * |u i| := by
          simp_rw [abs_mul]
    _ ≤ ∑ _i : Fin (d + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hnorm_v : ‖normalizedMomentCurve d t‖ = 1 := norm_normalizedMomentCurve d t
          have hv_i : |normalizedMomentCurve d t i| ≤ 1 := by
            calc
              |normalizedMomentCurve d t i| = ‖normalizedMomentCurve d t i‖ := by
                rw [Real.norm_eq_abs]
              _ ≤ ‖normalizedMomentCurve d t‖ := norm_le_pi_norm _ i
              _ = 1 := hnorm_v
          have hu_i : |u i| ≤ 1 := by
            calc
              |u i| = ‖u i‖ := by rw [Real.norm_eq_abs]
              _ ≤ ‖u‖ := norm_le_pi_norm _ i
              _ = 1 := hu
          have hmul : |normalizedMomentCurve d t i| * |u i| ≤ (1 : ℝ) * 1 := by
            exact mul_le_mul hv_i hu_i (abs_nonneg _) zero_le_one
          simpa using hmul
    _ = d + 1 := by simp

/-- For any unit-vector configuration, one of the finitely many candidate
    directions has strictly positive projection on every vector. -/
theorem exists_candidate_positive_projection (n : ℕ)
    (U : {p : Fin n × Fin n // p.1 ≠ p.2} → Fin (d + 1) → ℝ)
    (hU : ∀ p, ‖U p‖ = 1) :
    ∃ t ∈ universalProjectionCandidates n d,
      ∀ p : {q : Fin n × Fin n // q.1 ≠ q.2}, 0 < momentProjection d t (U p) := by
  let S : Finset (Fin (d + 1) → ℝ) := Finset.univ.image U
  have hS_nonzero : ∀ u ∈ S, u ≠ 0 := by
    intro u hu hzero
    rcases Finset.mem_image.mp hu with ⟨p, -, rfl⟩
    have : ‖U p‖ ≠ 0 := by simp [hU p]
    exact this (by simpa [hzero])
  obtain ⟨t, htS, htnz⟩ := exists_nonorthogonal_moment_in_candidates (d := d) S hS_nonzero
  have hS_card : S.card ≤ n * n := by
    calc
      S.card ≤ (Finset.univ : Finset {q : Fin n × Fin n // q.1 ≠ q.2}).card := Finset.card_image_le
      _ = Fintype.card {q : Fin n × Fin n // q.1 ≠ q.2} := by simp
      _ ≤ Fintype.card (Fin n × Fin n) := Fintype.card_subtype_le _
      _ = n * n := by simp
  have ht : t ∈ universalProjectionCandidates n d := by
    rcases Finset.mem_image.mp htS with ⟨m, hm, rfl⟩
    have hm' : m < S.card * d + 1 := by simpa using hm
    have hm'' : m < n * n * d + 1 := by
      have hcard : S.card * d + 1 ≤ n * n * d + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_right d hS_card) 1
      exact Nat.lt_of_lt_of_le hm' hcard
    simp [universalProjectionCandidates, Nat.lt_succ_iff.mp hm'']
  refine ⟨t, ht, ?_⟩
  intro p
  have hp_mem : U p ∈ S := Finset.mem_image.mpr ⟨p, by simp, rfl⟩
  have hsum_ne : ∑ i : Fin (d + 1), U p i * t ^ (i : ℕ) ≠ 0 := htnz (U p) hp_mem
  have hscaled :
      (∑ i : Fin (d + 1), normalizedMomentCurve d t i * U p i) =
        ‖momentCurve d t‖⁻¹ * ∑ i : Fin (d + 1), U p i * t ^ (i : ℕ) := by
    unfold normalizedMomentCurve momentCurve
    simp_rw [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold momentProjection
  rw [hscaled]
  apply abs_pos.mpr
  apply mul_ne_zero
  · exact inv_ne_zero (norm_ne_zero_iff.mpr (momentCurve_ne_zero d t))
  · exact hsum_ne

/-- A finite product is controlled by any chosen factor times a uniform bound
    on all factors. -/
theorem prod_le_factor_mul_pow_card {α : Type} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (B : ℝ) (p : α)
    (h0 : ∀ q, 0 ≤ f q) (hB : ∀ q, f q ≤ B) (hB1 : 1 ≤ B) :
    (∏ q, f q) ≤ f p * B ^ Fintype.card α := by
  have hp : p ∈ (Finset.univ : Finset α) := Finset.mem_univ p
  calc
    (∏ q, f q) = f p * Finset.prod (Finset.univ.erase p) f := by
      symm
      simpa using (Finset.mul_prod_erase (Finset.univ : Finset α) f hp)
    _ ≤ f p * Finset.prod (Finset.univ.erase p) (fun _ => B) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.prod_le_prod (fun q hq => h0 q) (fun q hq => hB q)
      · exact h0 p
    _ = f p * B ^ ((Finset.univ.erase p).card) := by simp
    _ ≤ f p * B ^ Fintype.card α := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ hB1 (by
          have : (Finset.univ.erase p).card ≤ Fintype.card α := by
            simpa [Finset.card_univ] using Nat.pred_le (Fintype.card α)
          exact this)
      · exact h0 p

/-- The universal projection constant: among finitely many normalized
    moment-curve directions, one works uniformly for every configuration of
    unit vectors. -/
theorem exists_universal_projection_constant (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (U : {p : Fin n × Fin n // p.1 ≠ p.2} → Fin (d + 1) → ℝ),
        (∀ p, ‖U p‖ = 1) →
        ∃ t ∈ universalProjectionCandidates n d,
          ∀ p, c ≤
            |∑ i : Fin (d + 1),
                normalizedMomentCurve d t i * U p i| := by
  let P := {p : Fin n × Fin n // p.1 ≠ p.2}
  let cand := universalProjectionCandidates n d
  let K : Set (P → Fin (d + 1) → ℝ) :=
    Set.univ.pi (fun _ => Metric.sphere (0 : Fin (d + 1) → ℝ) 1)
  have hcand_ne : cand.Nonempty := by
    refine ⟨0, ?_⟩
    simp [cand, universalProjectionCandidates]
  let G : (P → Fin (d + 1) → ℝ) → ℝ :=
    cand.sup' hcand_ne (fun t U => ∏ p : P, momentProjection d t (U p))
  have hprod_cont : ∀ t : ℝ, Continuous (fun U : P → Fin (d + 1) → ℝ =>
      ∏ p : P, momentProjection d t (U p)) := by
    intro t
    simpa using
      (continuous_finset_prod (Finset.univ : Finset P) (fun p hp =>
        by
          unfold momentProjection
          apply Continuous.abs
          refine continuous_finset_sum Finset.univ ?_
          intro i hi
          exact continuous_const.mul ((continuous_apply i).comp (continuous_apply p))))
  have hG_cont : Continuous G := by
    dsimp [G]
    exact Continuous.finset_sup' hcand_ne (fun t ht => hprod_cont t)
  have hK_compact : IsCompact K := by
    dsimp [K]
    simpa using
      isCompact_univ_pi (fun _ : P => isCompact_sphere (0 : Fin (d + 1) → ℝ) 1)
  have hK_nonempty : K.Nonempty := by
    refine ⟨fun _ => normalizedMomentCurve d 0, ?_⟩
    rw [Set.mem_univ_pi]
    intro p
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_normalizedMomentCurve]
  have hG_pos : ∀ U ∈ K, 0 < G U := by
    intro U hUK
    have hU : ∀ p : P, ‖U p‖ = 1 := by
      intro p
      have hp : U p ∈ Metric.sphere (0 : Fin (d + 1) → ℝ) 1 := (Set.mem_univ_pi.mp hUK) p
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hp
      exact hp
    obtain ⟨t, ht, hpos⟩ := exists_candidate_positive_projection (d := d) n U hU
    have hprod_pos : 0 < ∏ p : P, momentProjection d t (U p) := by
      simpa using
        (Finset.prod_pos (s := (Finset.univ : Finset P)) (fun p hp => hpos p))
    have hsup_ge : (∏ p : P, momentProjection d t (U p)) ≤ G U := by
      simpa [G] using
        (Finset.le_sup' (s := cand) (f := fun t => ∏ p : P, momentProjection d t (U p)) ht)
    dsimp [G]
    exact lt_of_lt_of_le hprod_pos hsup_ge
  obtain ⟨Umin, hUminK, hUmin_min⟩ := hK_compact.exists_isMinOn hK_nonempty hG_cont.continuousOn
  let c : ℝ := G Umin / (d + 1 : ℝ) ^ Fintype.card P
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (hG_pos Umin hUminK) (pow_pos (by positivity) _)
  refine ⟨c, hc_pos, ?_⟩
  intro U hU
  have hUK : U ∈ K := by
    rw [Set.mem_univ_pi]
    intro p
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hU p
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image cand (fun t => ∏ p : P, momentProjection d t (U p)) hcand_ne
  have hGU_eq : G U = ∏ p : P, momentProjection d t (U p) := by
    apply le_antisymm
    · simpa [G] using ((Finset.sup'_le_iff hcand_ne (fun b => ∏ p : P, momentProjection d b (U p))).2 hmax)
    · simpa [G] using
        (Finset.le_sup' (s := cand) (f := fun t => ∏ p : P, momentProjection d t (U p)) ht)
  refine ⟨t, ht, ?_⟩
  intro p
  have hupper :
      (∏ q : P, momentProjection d t (U q)) ≤
        momentProjection d t (U p) * (d + 1 : ℝ) ^ Fintype.card P := by
    refine prod_le_factor_mul_pow_card
      (f := fun q : P => momentProjection d t (U q)) (B := (d + 1 : ℝ)) (p := p)
      (h0 := fun q => abs_nonneg _)
      (hB := fun q => momentProjection_le_dim (d := d) t (U q) (hU q))
      (hB1 := by
        have hd : (0 : ℝ) ≤ d := by positivity
        linarith)
  have hmin_le :
      G Umin ≤ momentProjection d t (U p) * (d + 1 : ℝ) ^ Fintype.card P := by
    calc
      G Umin ≤ G U := hUmin_min hUK
      _ = ∏ q : P, momentProjection d t (U q) := hGU_eq
      _ ≤ momentProjection d t (U p) * (d + 1 : ℝ) ^ Fintype.card P := hupper
  dsimp [c]
  have hpow_pos : 0 < (d + 1 : ℝ) ^ Fintype.card P := pow_pos (by positivity) _
  have hc_le : c ≤ momentProjection d t (U p) := by
    exact (div_le_iff₀ hpow_pos).2 hmin_le
  simpa [momentProjection] using hc_le

/-! ### Step 3: Construct the rotation matrix -/

/-- Extend a Euclidean unit vector to an orthonormal basis and construct
    an orthogonal matrix with that vector as the first row. -/
theorem exists_orthogonal_matrix_with_first_row
    (v : Fin (d + 1) → ℝ) (hv : ∑ j : Fin (d + 1), v j ^ 2 = 1) :
    ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 ∧ R.det = 1 ∧
      ∀ j, R 0 j = v j := by
  let vE : EuclideanSpace ℝ (Fin (d + 1)) := (WithLp.equiv 2 (Fin (d + 1) → ℝ)).symm v
  have hvE : ‖vE‖ = 1 := by
    rw [PiLp.norm_eq_sum (show 0 < (2 : ENNReal).toReal by norm_num)]
    simp [vE, hv, Real.norm_eq_abs]
  let w : Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) := fun i => if i = 0 then vE else 0
  have hw : Orthonormal ℝ (({0} : Set (Fin (d + 1))).restrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin (d + 1)) = 0 := i.2
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp [w, hi, hvE]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin (d + 1))) (ι := Fin (d + 1)) (by simp) (v := w)
    (s := ({0} : Set (Fin (d + 1)))) hw
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun i j => (b i).ofLp j
  have hMMt : M * M.transpose = 1 := by
    ext i j
    calc
      (M * M.transpose) i j = ∑ x : Fin (d + 1), (b i).ofLp x * (b j).ofLp x := by
        simp [M, Matrix.mul_apply]
      _ = inner ℝ (b i) (b j) := by
        rw [PiLp.inner_apply]
        simp [RCLike.inner_apply, mul_comm]
      _ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp b.orthonormal) i j
      _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i j := by simp [Matrix.one_apply]
  have hMtM : M.transpose * M = 1 := (mul_eq_one_comm.mp hMMt)
  have hb0 : b 0 = vE := by
    simpa [w] using hb 0 (by simp)
  have hdet_cases : M.det = 1 ∨ M.det = -1 := by
    have hdet_sq : M.det * M.det = 1 := by
      have := congrArg Matrix.det hMMt
      simpa [Matrix.det_mul, Matrix.det_transpose] using this
    have hfac : (M.det - 1) * (M.det + 1) = 0 := by
      nlinarith [hdet_sq]
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left
      linarith
    · right
      linarith
  rcases hdet_cases with hdet | hdet
  · refine ⟨M, hMtM, hdet, ?_⟩
    intro j
    simpa [M, vE, hb0] using congrFun hb0 j
  · let s : Fin (d + 1) → ℝ := fun i => if i = ⟨1, by
      have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      omega⟩ then (-1 : ℝ) else 1
    let D : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.diagonal s
    let R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := D * M
    refine ⟨R, ?_, ?_, ?_⟩
    · have hDD : D * D = 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_mul]
          by_cases hi1 : i = ⟨1, by
              have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
              omega⟩
          · simp [D, s, hi1]
          · simp [D, s, hi1]
        · rw [Matrix.diagonal_mul]
          simp [D, hij]
      calc
        R.transpose * R = (D * M).transpose * (D * M) := by rfl
        _ = M.transpose * (D.transpose * (D * M)) := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = M.transpose * ((D.transpose * D) * M) := by simp [Matrix.mul_assoc]
        _ = M.transpose * ((D * D) * M) := by simp [D]
        _ = M.transpose * (1 * M) := by rw [hDD]
        _ = M.transpose * M := by simp
        _ = 1 := hMtM
    · have hdetD : D.det = -1 := by
        simp [D, s, Matrix.det_diagonal]
      calc
        R.det = D.det * M.det := by simp [R, Matrix.det_mul]
        _ = 1 := by nlinarith [hdetD, hdet]
    · intro j
      have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by
          have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
          omega⟩ := by
        rw [Fin.ne_iff_vne]
        norm_num
      simp [R, D, Matrix.diagonal_mul, s, h01, M, vE, hb0]

/-! ### Main theorem -/

/-- **Universal Projection Lemma (Ruelle's Lemma)**

    For any n points in ℝ^{d+1}, there exists a universal constant c > 0
    and a proper rotation R ∈ SO(d+1) such that the time-axis projections
    of ALL pairwise differences are bounded below by c times their full
    Euclidean distance. -/
theorem exists_universal_time_projection' (d n : ℕ) [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ∃ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
        R.transpose * R = 1 ∧ R.det = 1 ∧
        ∀ i j : Fin n, i ≠ j →
          c * ‖x i - x j‖ ≤ |(R.mulVec (x i - x j)) 0| := by
  -- Get the universal projection constant for normalized candidate directions.
  obtain ⟨c₀, hc₀_pos, hproj⟩ := exists_universal_projection_constant (d := d) n
  let c : ℝ := c₀ / (d + 1 : ℝ)
  have hc_pos : 0 < c := by
    exact div_pos hc₀_pos (by positivity)
  refine ⟨c, hc_pos, fun x => ?_⟩
  let P := {q : Fin n × Fin n // q.1 ≠ q.2}
  let pairDiff : P → Fin (d + 1) → ℝ := fun p => x p.1.1 - x p.1.2
  let U : P → Fin (d + 1) → ℝ := fun p =>
    if hp : pairDiff p = 0 then normalizedMomentCurve d 0 else ‖pairDiff p‖⁻¹ • pairDiff p
  have hU : ∀ p, ‖U p‖ = 1 := by
    intro p
    by_cases hp : pairDiff p = 0
    · simp [U, hp, norm_normalizedMomentCurve]
    · have hpn : ‖pairDiff p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
      calc
        ‖U p‖ = |‖pairDiff p‖⁻¹| * ‖pairDiff p‖ := by
          simp [U, hp, norm_smul]
        _ = 1 := by
          rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          field_simp [hpn]
  obtain ⟨t, ht, hbound⟩ := hproj U hU
  let v0 : Fin (d + 1) → ℝ := normalizedMomentCurve d t
  let s : ℝ := ∑ j : Fin (d + 1), v0 j ^ 2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv0_ne_zero : v0 0 ≠ 0 := by
    dsimp [v0, normalizedMomentCurve, momentCurve]
    simp [momentCurve_ne_zero, inv_ne_zero]
  have h0sq_pos : 0 < v0 0 ^ 2 := sq_pos_of_ne_zero hv0_ne_zero
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lt_of_lt_of_le h0sq_pos
      (Finset.single_le_sum (fun _ _ => sq_nonneg _) (by simp))
  let e : ℝ := Real.sqrt s
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.sqrt_pos.2 hs_pos
  have he_nonneg : 0 ≤ e := le_of_lt he_pos
  have hv0_coord_le_one : ∀ j : Fin (d + 1), |v0 j| ≤ 1 := by
    intro j
    calc
      |v0 j| = ‖v0 j‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖v0‖ := norm_le_pi_norm _ j
      _ = 1 := norm_normalizedMomentCurve d t
  have hs_le : s ≤ d + 1 := by
    dsimp [s]
    calc
      ∑ j : Fin (d + 1), v0 j ^ 2 ≤ ∑ _j : Fin (d + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj_le : |v0 j| ≤ 1 := hv0_coord_le_one j
        have hj_sq : v0 j ^ 2 ≤ 1 := by
          have hsq_abs : |v0 j| ^ 2 ≤ 1 := by
            nlinarith [abs_nonneg (v0 j), hj_le]
          simpa [sq_abs] using hsq_abs
        exact hj_sq
      _ = d + 1 := by simp
  have he_le : e ≤ d + 1 := by
    have hs_eq : e ^ 2 = s := by
      dsimp [e]
      rw [Real.sq_sqrt hs_nonneg]
    nlinarith [hs_le]
  let v : Fin (d + 1) → ℝ := e⁻¹ • v0
  have hv : ∑ j : Fin (d + 1), v j ^ 2 = 1 := by
    have hs_ne : s ≠ 0 := by linarith
    calc
      ∑ j : Fin (d + 1), v j ^ 2 = ∑ j : Fin (d + 1), (e⁻¹)^2 * (v0 j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [v]
        ring
      _ = (e⁻¹)^2 * s := by
        dsimp [s]
        rw [Finset.mul_sum]
      _ = 1 := by
        dsimp [e]
        have hsqrt : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs_nonneg
        field_simp [hs_ne]
        nlinarith
  obtain ⟨R, hRtR, hdetR, hrow⟩ := exists_orthogonal_matrix_with_first_row (d := d) v hv
  refine ⟨R, hRtR, hdetR, ?_⟩
  intro i j hij
  let y : Fin (d + 1) → ℝ := x i - x j
  by_cases hy : y = 0
  · simp [c, y, hy]
  · let p : P := ⟨(i, j), hij⟩
    have hU_bound : c₀ ≤ |∑ k : Fin (d + 1), v0 k * U p k| := by
      simpa [v0] using hbound p
    have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hy_norm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hU_formula : U p = ‖y‖⁻¹ • y := by
      ext k
      simp [U, pairDiff, p, y, hy]
    have hsum_scale :
        ∑ k : Fin (d + 1), v0 k * U p k = ‖y‖⁻¹ * ∑ k : Fin (d + 1), v0 k * y k := by
      rw [hU_formula]
      simp_rw [Pi.smul_apply, smul_eq_mul]
      calc
        ∑ k : Fin (d + 1), v0 k * (‖y‖⁻¹ * y k)
            = ∑ k : Fin (d + 1), ‖y‖⁻¹ * (v0 k * y k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ = ‖y‖⁻¹ * ∑ k : Fin (d + 1), v0 k * y k := by
              rw [Finset.mul_sum]
    have habs_eq :
        |∑ k : Fin (d + 1), v0 k * U p k| = ‖y‖⁻¹ * |∑ k : Fin (d + 1), v0 k * y k| := by
      rw [hsum_scale, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have hsum_lower : c₀ * ‖y‖ ≤ |∑ k : Fin (d + 1), v0 k * y k| := by
      rw [habs_eq] at hU_bound
      have hmul := mul_le_mul_of_nonneg_right hU_bound hy_norm_pos.le
      have hcancel : ‖y‖⁻¹ * |∑ k : Fin (d + 1), v0 k * y k| * ‖y‖ = |∑ k : Fin (d + 1), v0 k * y k| := by
        calc
          ‖y‖⁻¹ * |∑ k : Fin (d + 1), v0 k * y k| * ‖y‖
              = |∑ k : Fin (d + 1), v0 k * y k| * (‖y‖⁻¹ * ‖y‖) := by ring
          _ = |∑ k : Fin (d + 1), v0 k * y k| := by
              field_simp [hy_norm_ne]
      simpa [mul_assoc, hcancel] using hmul
    have hmulVec0 :
        (R.mulVec y) 0 = ∑ k : Fin (d + 1), v k * y k := by
      simpa [Matrix.mulVec, dotProduct, hrow]
    have hmulVec0' :
        (R.mulVec y) 0 = e⁻¹ * ∑ k : Fin (d + 1), v0 k * y k := by
      rw [hmulVec0]
      calc
        ∑ k : Fin (d + 1), v k * y k = ∑ k : Fin (d + 1), e⁻¹ * (v0 k * y k) := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [v]
          ring
        _ = e⁻¹ * ∑ k : Fin (d + 1), v0 k * y k := by
          rw [Finset.mul_sum]
    have hrow_lower : (c₀ / e) * ‖y‖ ≤ |(R.mulVec y) 0| := by
      rw [hmulVec0', abs_mul, abs_of_nonneg (inv_nonneg.mpr he_nonneg)]
      have hmul := mul_le_mul_of_nonneg_left hsum_lower (inv_nonneg.mpr he_nonneg)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hc_le' : c ≤ c₀ / e := by
      dsimp [c]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (by positivity) he_pos).2 he_le) hc₀_pos.le
    calc
      c * ‖x i - x j‖ = c * ‖y‖ := by rfl
      _ ≤ (c₀ / e) * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right hc_le' hy_norm_pos.le
      _ ≤ |(R.mulVec y) 0| := hrow_lower
      _ = |(R.mulVec (x i - x j)) 0| := by rfl
