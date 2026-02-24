/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.AbsConvex
import OSReconstruction.Wightman.NuclearSpaces.NuclearOperator

/-!
# Nuclear Spaces

This file defines nuclear spaces using Grothendieck/Pietsch characterization.

## Main Definitions

* `NuclearSpace` - A locally convex space E is nuclear if for every continuous seminorm p,
  there exists a continuous seminorm q ≥ p such that p is "nuclearly dominated" by q.
* `NuclearFrechet` - A nuclear Fréchet space presented via seminorms with nuclear steps.

## Mathematical Background

A locally convex topological vector space E is **nuclear** (Grothendieck) if its topology
is defined by a family of seminorms {p_α} such that for every p_α, there exists p_β ≥ p_α
with the canonical map from the completion of E/ker(p_β) to E/ker(p_α) being a nuclear
operator.

Equivalent characterizations:
1. (Grothendieck) Via nuclear maps between seminorm completions
2. (Pietsch) For every continuous seminorm p, there exist fₙ ∈ E* and cₙ ≥ 0 with
   Σ cₙ < ∞ such that p(x) ≤ Σ |fₙ(x)| · cₙ and each fₙ continuous
3. (Schwartz) Projective limit of Hilbert spaces with Hilbert-Schmidt connecting maps

Key examples: S(ℝⁿ), C^∞(M), distributions, finite-dimensional spaces.
Non-examples: infinite-dimensional Banach spaces.

## References

* Grothendieck, "Produits tensoriels topologiques et espaces nucléaires" (1955)
* Pietsch, "Nuclear Locally Convex Spaces" (1972)
* Trèves, "Topological Vector Spaces, Distributions and Kernels" (1967), Ch. 50
-/

noncomputable section

open scoped NNReal Topology
open Filter

/-! ### Nuclear Space Definition (Pietsch characterization) -/

/-- A locally convex topological vector space over ℝ is **nuclear** if for every continuous
    seminorm p, there exist continuous linear functionals (fₙ : E →L[ℝ] ℝ) and non-negative
    reals (cₙ) with Σ cₙ < ∞, and a continuous seminorm q ≥ p, such that:
    (1) p(x) ≤ Σₙ |fₙ(x)| · cₙ for all x
    (2) |fₙ(x)| ≤ q(x) for all x, n

    This is Pietsch's characterization, equivalent to Grothendieck's definition that
    the canonical map E_q → E_p between seminorm completions is nuclear.

    We follow the `LocallyConvexSpace` pattern in Mathlib for the type class binders. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear_dominance : ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧
      Summable c ∧
      (∀ n x, ‖f n x‖ ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n)

/-! ### Basic Properties of Nuclear Spaces -/

namespace NuclearSpace

/-- Helper: the triangle inequality for seminorms on finite sums. -/
private theorem seminorm_finset_sum_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Seminorm ℝ V) {ι : Type*} (s : Finset ι) (g : ι → V) :
    p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp [map_zero]
  | cons a s has ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    calc p (g a + ∑ i ∈ s, g i) ≤ p (g a) + p (∑ i ∈ s, g i) := map_add_le_add p _ _
      _ ≤ p (g a) + ∑ i ∈ s, p (g i) := by linarith

/-- Helper: evaluation of a finset sum of seminorms distributes. -/
private theorem finset_sum_seminorm_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} (s : Finset ι) (q : ι → Seminorm ℝ V) (x : V) :
    (s.sum q) x = s.sum (fun i => (q i) x) := by
  induction s using Finset.cons_induction with
  | empty => simp [Seminorm.zero_apply]
  | cons a s has ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Seminorm.add_apply, ih]

/-- Finite-dimensional spaces are nuclear.

    The proof uses a basis b₁,...,bₙ with coordinate functionals φᵢ. Given any
    continuous seminorm p, we construct q = p + Σᵢ |φᵢ| as the dominating seminorm,
    and use φᵢ, cᵢ = p(bᵢ) for the nuclear decomposition. The triangle inequality
    p(x) = p(Σ φᵢ(x)·bᵢ) ≤ Σ |φᵢ(x)|·p(bᵢ) provides the nuclear bound. -/
theorem finiteDimensional (V : Type*) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [FiniteDimensional ℝ V] [T2Space V] : NuclearSpace V where
  nuclear_dominance := by
    intro p hp
    let d := Module.finrank ℝ V
    let b := Module.finBasis ℝ V
    -- Coordinate seminorms: x ↦ ‖b.coord i x‖
    let coordSemi : Fin d → Seminorm ℝ V :=
      fun i => (normSeminorm ℝ ℝ).comp (b.coord i)
    -- ℓ¹ coordinate seminorm: ell1(x) = Σ_i ‖b.coord i x‖
    let ell1 : Seminorm ℝ V := Finset.univ.sum coordSemi
    -- Helper: ell1 x = Σ_i ‖b.coord i x‖
    have ell1_eq : ∀ x, ell1 x = ∑ i : Fin d, ‖(b.coord i) x‖ := by
      intro x
      rw [show ell1 x = Finset.univ.sum (fun i => coordSemi i x) from
        finset_sum_seminorm_apply _ _ _]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [coordSemi, Seminorm.comp_apply, coe_normSeminorm]
    -- ell1 is continuous
    have ell1_cont : Continuous (⇑ell1 : V → ℝ) := by
      rw [show (⇑ell1 : V → ℝ) = fun x => ∑ i : Fin d, ‖(b.coord i) x‖ from
        funext ell1_eq]
      exact continuous_finset_sum _ fun i _ =>
        continuous_norm.comp (b.coord i).continuous_of_finiteDimensional
    -- Dominating seminorm q = p + ell1
    refine ⟨p + ell1, ?_, ?_, ?_⟩
    · -- q is continuous
      rw [show (⇑(p + ell1) : V → ℝ) = fun x => p x + ell1 x from
        funext (Seminorm.add_apply p ell1)]
      exact Continuous.add hp ell1_cont
    · -- q ≥ p
      intro x; rw [Seminorm.add_apply]; linarith [apply_nonneg ell1 x]
    · -- Nuclear decomposition
      -- Name f and c to make reasoning about dite tractable
      let f : ℕ → (V →L[ℝ] ℝ) := fun k =>
        if h : k < d then
          ⟨b.coord ⟨k, h⟩, (b.coord ⟨k, h⟩).continuous_of_finiteDimensional⟩
        else 0
      let c : ℕ → ℝ := fun k => if h : k < d then p (b ⟨k, h⟩) else 0
      have hf_lt : ∀ k (h : k < d), f k =
          ⟨b.coord ⟨k, h⟩, (b.coord ⟨k, h⟩).continuous_of_finiteDimensional⟩ :=
        fun k h => dif_pos h
      have hf_ge : ∀ k, ¬(k < d) → f k = 0 := fun k h => dif_neg h
      have hc_lt : ∀ k (h : k < d), c k = p (b ⟨k, h⟩) := fun k h => dif_pos h
      have hc_ge : ∀ k, ¬(k < d) → c k = 0 := fun k h => dif_neg h
      refine ⟨f, c, ?_, ?_, ?_, ?_⟩
      · -- c ≥ 0
        intro k
        by_cases h : k < d
        · rw [hc_lt k h]; exact apply_nonneg p _
        · rw [hc_ge k h]
      · -- Summable c (finitely supported)
        exact summable_of_ne_finset_zero (s := Finset.range d)
          (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            exact hc_ge k (not_lt.mpr hk))
      · -- ‖f k x‖ ≤ q x
        intro k x
        by_cases h : k < d
        · -- k < d: ‖b.coord ⟨k,h⟩ x‖ ≤ (p + ell1) x
          rw [hf_lt k h]
          rw [Seminorm.add_apply]
          simp only [ContinuousLinearMap.coe_mk']
          have hle : ‖(b.coord ⟨k, h⟩) x‖ ≤ ell1 x := by
            rw [ell1_eq]
            exact Finset.single_le_sum
              (fun (i : Fin d) _ => norm_nonneg ((b.coord i) x))
              (Finset.mem_univ (⟨k, h⟩ : Fin d))
          linarith [apply_nonneg p x]
        · -- k ≥ d: ‖0 x‖ = 0 ≤ q x
          rw [hf_ge k h]
          simp only [ContinuousLinearMap.zero_apply, norm_zero]
          exact apply_nonneg (p + ell1) x
      · -- p x ≤ Σ' k, ‖f k x‖ * c k
        intro x
        -- Step 1: Triangle inequality: p x ≤ ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i)
        have hdecomp : x = ∑ i : Fin d, (b.coord i x) • (b i) := by
          change x = ∑ i : Fin d, (b.repr x) i • (b i)
          exact (b.sum_repr x).symm
        have hbound : p x ≤ ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) := by
          calc p x = p (∑ i : Fin d, (b.coord i x) • (b i)) := by
                  conv_lhs => rw [hdecomp]
            _ ≤ ∑ i : Fin d, p ((b.coord i x) • (b i)) := seminorm_finset_sum_le p _ _
            _ = ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) := by
                apply Finset.sum_congr rfl; intro i _
                exact map_smul_eq_mul p _ _
        -- Step 2: The tsum equals the Fin d sum
        have hzero : ∀ k, ¬(k < d) → ‖f k x‖ * c k = 0 := by
          intro k hk; rw [hf_ge k hk, hc_ge k hk]; simp
        have htsum : ∑' k, ‖f k x‖ * c k =
            (Finset.range d).sum (fun k => ‖f k x‖ * c k) :=
          tsum_eq_sum (fun k hk => by
            simp only [Finset.mem_range, not_lt] at hk
            exact hzero k (not_lt.mpr hk))
        rw [htsum, ← Fin.sum_univ_eq_sum_range]
        -- Convert the Fin d sum terms to match hbound
        have hterm : ∀ (i : Fin d),
            ‖f i.val x‖ * c i.val = ‖(b.coord i) x‖ * p (b i) := by
          intro ⟨k, hk⟩
          simp only [hf_lt k hk, hc_lt k hk, ContinuousLinearMap.coe_mk']
        calc ∑ i : Fin d, ‖f i.val x‖ * c i.val
            = ∑ i : Fin d, ‖(b.coord i) x‖ * p (b i) :=
              Finset.sum_congr rfl (fun i _ => hterm i)
          _ ≥ p x := hbound

-- Every continuous seminorm on a subspace is dominated by the restriction
-- of a continuous seminorm on the ambient space. This follows from the
-- subspace topology being the initial topology with respect to the inclusion.
--
-- Mathematically: if E is a TVS and S ≤ E carries the subspace topology, then
-- for any continuous seminorm p on S, there exists a continuous seminorm r on E
-- such that p(s) ≤ r(ι(s)) for all s ∈ S. This is because the open ball
-- {s | p(s) < 1} is open in S, hence contains a set of the form S ∩ U where
-- U is open in E, and from U one extracts a continuous seminorm on E.

/-- Helper: Given a convex neighborhood W of 0 in E such that ι(S) ∩ W ⊆ {p < 1},
    construct a continuous seminorm on E dominating p on S.

    The proof requires finding a balanced convex subset of W (via nhds_basis_balanced),
    constructing gaugeSeminorm from it, and proving the domination via a scaling argument.
    Blocked by: gaugeSeminorm requires Balanced, and the scaling argument needs
    gauge_lt_one_of_mem_interior + absorbent_nhds_zero. -/
private lemma gauge_dominates_on_subspace_of_convex_nhd
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Submodule ℝ E} (p : Seminorm ℝ S)
    (W : Set E) (hW_conv : Convex ℝ W) (hW_nhd : W ∈ nhds (0 : E))
    (hSW : ∀ s : S, S.subtype s ∈ W → p s < 1) :
    ∃ (r : Seminorm ℝ E), Continuous r ∧ ∀ s : S, p s ≤ r (S.subtype s) := by
  sorry

theorem subspace_seminorm_dominated (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E]
    (S : Submodule ℝ E) (p : Seminorm ℝ S) (hp : Continuous p) :
    ∃ (r : Seminorm ℝ E), Continuous r ∧ ∀ s : S, p s ≤ r (S.subtype s) := by
  -- Step 1: {s | p(s) < 1} is open in S (subspace topology)
  have h1 : IsOpen { s : S | p s < 1 } := isOpen_lt hp continuous_const
  -- Step 2: In the subspace topology, this open set is the preimage of an open set in E
  rw [isOpen_induced_iff] at h1
  obtain ⟨V, hV_open, hV_eq⟩ := h1
  -- Step 3: 0 ∈ V (since p(0) = 0 < 1)
  have h0V : (0 : E) ∈ V := by
    have h0S : (0 : S) ∈ { s : S | p s < 1 } := by simp [map_zero]
    have : (0 : S) ∈ Subtype.val ⁻¹' V := hV_eq ▸ h0S
    simpa using this
  -- Step 4: For s ∈ S with ι(s) ∈ V, p(s) < 1
  have hVp : ∀ s : S, (s : E) ∈ V → p s < 1 := by
    intro s hs
    have : s ∈ Subtype.val ⁻¹' V := hs
    rw [hV_eq] at this; exact this
  -- Step 5: V is a neighborhood of 0 in E. Use the convex basis of LocallyConvexSpace
  -- to find W convex with W ∈ nhds 0 and W ⊆ V.
  have hV_nhd : V ∈ nhds (0 : E) := hV_open.mem_nhds h0V
  -- The convex basis at 0 gives a convex set W ∈ nhds 0 with W ⊆ V
  have hbasis := (@LocallyConvexSpace.convex_basis ℝ E _ _ _ _ _ ‹_› (0 : E)).mem_iff.mp hV_nhd
  obtain ⟨W, ⟨hW_nhd, hW_conv⟩, hWV⟩ := hbasis
  -- Step 6: Apply gauge construction helper
  exact gauge_dominates_on_subspace_of_convex_nhd p W hW_conv hW_nhd
    (fun s hs => hVp s (hWV hs))

/-- A closed subspace of a nuclear space is nuclear. -/
theorem subspace_nuclear (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [NuclearSpace E] [LocallyConvexSpace ℝ E]
    (S : Submodule ℝ E) (_hclosed : IsClosed (S : Set E)) :
    NuclearSpace S where
  nuclear_dominance p hp := by
    -- Step 1: p is dominated by a continuous seminorm on E restricted to S
    obtain ⟨r, hr_cont, hr_dom⟩ := subspace_seminorm_dominated E S p hp
    -- Step 2: Apply nuclearity of E to r
    obtain ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bound, hr_bound⟩ :=
      NuclearSpace.nuclear_dominance r hr_cont
    -- Step 3: Construct restricted seminorm and functionals
    refine ⟨q.comp S.subtype, ?_, ?_, fun n => (f n).comp S.subtypeL, c,
      hc_nn, hc_sum, ?_, ?_⟩
    · -- q.comp S.subtype is continuous
      exact hq_cont.comp S.subtypeL.continuous
    · -- q.comp S.subtype ≥ p
      intro s
      show p s ≤ q (S.subtype s)
      calc p s ≤ r (S.subtype s) := hr_dom s
        _ ≤ q (S.subtype s) := hq_ge _
    · -- ‖(f n).comp S.subtypeL s‖ ≤ (q.comp S.subtype) s
      intro n s
      simp only [Seminorm.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      exact hf_bound n (S.subtype s)
    · -- p(s) ≤ Σ' n, ‖(f n).comp S.subtypeL s‖ * c n
      intro s
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      calc p s ≤ r (S.subtype s) := hr_dom s
        _ ≤ ∑' n, ‖(f n) (S.subtype s)‖ * c n := hr_bound _

/-- Every continuous seminorm on a countable product is dominated by a finite sum
    of pullbacks of continuous seminorms on the factors. This is a consequence of
    the product topology being the initial topology with respect to the projections.

    Mathematically: if p is a continuous seminorm on Π_i E_i (product topology), then
    there exist a finite set F ⊆ ι, continuous seminorms r_i on E_i (for i ∈ F), such
    that p(x) ≤ ∑_{i ∈ F} r_i(x_i) for all x. -/
theorem product_seminorm_dominated (ι : Type*) [Countable ι]
    (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul ℝ (E i)]
    (p : Seminorm ℝ (∀ i, E i)) (hp : Continuous p) :
    ∃ (F : Finset ι) (r : ∀ i, Seminorm ℝ (E i)),
      (∀ i ∈ F, Continuous (r i)) ∧
      ∀ x : (∀ i, E i), p x ≤ ∑ i ∈ F, (r i) (x i) := by
  sorry

/-- If a seminorm p on a space V admits a "nuclear decomposition" -- meaning there is
    a dominating continuous seminorm q and sequences f_n, c_n with the nuclear bound --
    then p satisfies the NuclearSpace condition. This packages the existential. -/
private theorem nuclear_dominance_of_data {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V]
    (p : Seminorm ℝ V) (q : Seminorm ℝ V) (hq_cont : Continuous q)
    (hq_ge : ∀ x, p x ≤ q x)
    (f : ℕ → (V →L[ℝ] ℝ)) (c : ℕ → ℝ) (hc_nn : ∀ n, 0 ≤ c n)
    (hc_sum : Summable c) (hf_bound : ∀ n x, ‖f n x‖ ≤ q x)
    (hp_bound : ∀ x, p x ≤ ∑' n, ‖f n x‖ * c n) :
    ∃ (q' : Seminorm ℝ V), Continuous q' ∧ (∀ x, p x ≤ q' x) ∧
      ∃ (f' : ℕ → (V →L[ℝ] ℝ)) (c' : ℕ → ℝ),
        (∀ n, 0 ≤ c' n) ∧ Summable c' ∧
        (∀ n x, ‖f' n x‖ ≤ q' x) ∧ (∀ x, p x ≤ ∑' n, ‖f' n x‖ * c' n) :=
  ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bound, hp_bound⟩

/-- Even/odd interleaving ℕ ⊕ ℕ ≃ ℕ for combining nuclear decompositions. -/
private def sumEquiv : ℕ ⊕ ℕ ≃ ℕ where
  toFun | .inl n => 2 * n | .inr n => 2 * n + 1
  invFun n := if n % 2 = 0 then .inl (n / 2) else .inr (n / 2)
  left_inv x := by
    cases x with
    | inl n => simp
    | inr n =>
      have h : (2 * n + 1) % 2 = 1 := by omega
      simp [h]; omega
  right_inv n := by
    by_cases h : n % 2 = 0 <;> simp [h] <;> omega

/-- Combining two nuclear decompositions: if seminorms p₁ and p₂ on V each have
    nuclear decompositions (q₁, f₁, c₁) and (q₂, f₂, c₂), then p₁ + p₂ has a nuclear
    decomposition with dominating seminorm q₁ + q₂ and interleaved sequences. -/
theorem nuclear_sum_decomposition {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V]
    (p₁ p₂ : Seminorm ℝ V)
    (q₁ : Seminorm ℝ V) (hq₁_cont : Continuous q₁) (hq₁_ge : ∀ x, p₁ x ≤ q₁ x)
    (f₁ : ℕ → (V →L[ℝ] ℝ)) (c₁ : ℕ → ℝ) (hc₁_nn : ∀ n, 0 ≤ c₁ n) (hc₁_sum : Summable c₁)
    (hf₁_bound : ∀ n x, ‖f₁ n x‖ ≤ q₁ x) (hp₁_bound : ∀ x, p₁ x ≤ ∑' n, ‖f₁ n x‖ * c₁ n)
    (q₂ : Seminorm ℝ V) (hq₂_cont : Continuous q₂) (hq₂_ge : ∀ x, p₂ x ≤ q₂ x)
    (f₂ : ℕ → (V →L[ℝ] ℝ)) (c₂ : ℕ → ℝ) (hc₂_nn : ∀ n, 0 ≤ c₂ n) (hc₂_sum : Summable c₂)
    (hf₂_bound : ∀ n x, ‖f₂ n x‖ ≤ q₂ x) (hp₂_bound : ∀ x, p₂ x ≤ ∑' n, ‖f₂ n x‖ * c₂ n)
    (p : Seminorm ℝ V) (hp_le : ∀ x, p x ≤ p₁ x + p₂ x) :
    ∃ (q : Seminorm ℝ V), Continuous q ∧ (∀ x, p x ≤ q x) ∧
      ∃ (f : ℕ → (V →L[ℝ] ℝ)) (c : ℕ → ℝ),
        (∀ n, 0 ≤ c n) ∧ Summable c ∧
        (∀ n x, ‖f n x‖ ≤ q x) ∧ (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n) := by
  -- Dominating seminorm: q₁ + q₂
  refine ⟨q₁ + q₂, ?_, ?_, ?_⟩
  · -- Continuous
    show Continuous (⇑(q₁ + q₂))
    rw [show (⇑(q₁ + q₂) : V → ℝ) = fun x => q₁ x + q₂ x from
      funext (Seminorm.add_apply q₁ q₂)]
    exact Continuous.add hq₁_cont hq₂_cont
  · -- Dominates p
    intro x
    calc p x ≤ p₁ x + p₂ x := hp_le x
      _ ≤ q₁ x + q₂ x := add_le_add (hq₁_ge x) (hq₂_ge x)
      _ = (q₁ + q₂) x := (Seminorm.add_apply q₁ q₂ x).symm
  · -- Interleave the sequences via even/odd encoding
    let e := sumEquiv
    let f : ℕ → (V →L[ℝ] ℝ) := Sum.elim f₁ f₂ ∘ e.symm
    let c : ℕ → ℝ := Sum.elim c₁ c₂ ∘ e.symm
    refine ⟨f, c, ?_, ?_, ?_, ?_⟩
    · -- c ≥ 0
      intro n
      simp only [Function.comp, c]
      cases e.symm n with
      | inl k => exact hc₁_nn k
      | inr k => exact hc₂_nn k
    · -- Summable c
      show Summable (Sum.elim c₁ c₂ ∘ e.symm)
      rw [e.symm.summable_iff]
      exact Summable.sum (Sum.elim c₁ c₂)
        (by simp; exact hc₁_sum)
        (by simp; exact hc₂_sum)
    · -- ‖f n x‖ ≤ (q₁ + q₂) x
      intro n x
      simp only [Function.comp, f, Seminorm.add_apply]
      cases e.symm n with
      | inl k =>
        simp only [Sum.elim_inl]
        calc ‖f₁ k x‖ ≤ q₁ x := hf₁_bound k x
          _ ≤ q₁ x + q₂ x := le_add_of_nonneg_right (apply_nonneg q₂ x)
      | inr k =>
        simp only [Sum.elim_inr]
        calc ‖f₂ k x‖ ≤ q₂ x := hf₂_bound k x
          _ ≤ q₁ x + q₂ x := le_add_of_nonneg_left (apply_nonneg q₁ x)
    · -- p x ≤ Σ' n, ‖f n x‖ * c n
      intro x
      -- The interleaved tsum equals the sum of the two tsums
      -- Summability helpers for the interleaved terms
      have hsum₁ : Summable (fun n => ‖f₁ n x‖ * c₁ n) :=
        Summable.of_nonneg_of_le
          (fun n => mul_nonneg (norm_nonneg _) (hc₁_nn n))
          (fun n => mul_le_mul_of_nonneg_right (hf₁_bound n x) (hc₁_nn n))
          (hc₁_sum.hasSum.mul_left (q₁ x) |>.summable)
      have hsum₂ : Summable (fun n => ‖f₂ n x‖ * c₂ n) :=
        Summable.of_nonneg_of_le
          (fun n => mul_nonneg (norm_nonneg _) (hc₂_nn n))
          (fun n => mul_le_mul_of_nonneg_right (hf₂_bound n x) (hc₂_nn n))
          (hc₂_sum.hasSum.mul_left (q₂ x) |>.summable)
      have htsum : ∑' n, ‖f n x‖ * c n =
          (∑' n, ‖f₁ n x‖ * c₁ n) + (∑' n, ‖f₂ n x‖ * c₂ n) := by
        -- Convert ℕ-tsum to (ℕ ⊕ ℕ)-tsum via the equiv
        have heq : (fun n => ‖f n x‖ * c n) =
            (fun s : ℕ ⊕ ℕ => ‖Sum.elim f₁ f₂ s x‖ * Sum.elim c₁ c₂ s) ∘ e.symm := by
          ext n; simp [f, c, Function.comp]
        rw [heq]
        -- The tsum over ℕ via e.symm equals the tsum over ℕ ⊕ ℕ
        let g : ℕ ⊕ ℕ → ℝ := fun s => ‖(Sum.elim f₁ f₂ s) x‖ * Sum.elim c₁ c₂ s
        -- Eta-expand to enable rewriting
        show (∑' n, g (e.symm n)) = (∑' n, ‖f₁ n x‖ * c₁ n) + (∑' n, ‖f₂ n x‖ * c₂ n)
        rw [Equiv.tsum_eq e.symm g]
        -- Now split the tsum over ℕ ⊕ ℕ into sum of tsums
        exact Summable.tsum_sum hsum₁ hsum₂
      rw [htsum]
      calc p x ≤ p₁ x + p₂ x := hp_le x
        _ ≤ (∑' n, ‖f₁ n x‖ * c₁ n) + (∑' n, ‖f₂ n x‖ * c₂ n) :=
          add_le_add (hp₁_bound x) (hp₂_bound x)

/-- Pulling back a nuclear decomposition through a continuous linear map.
    If p on F has a nuclear decomposition (q, f_n, c_n), and L : E →L[ℝ] F is continuous,
    then p.comp L on E has a nuclear decomposition (q.comp L, f_n ∘ L, c_n). -/
private theorem nuclear_pullback {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    (p : Seminorm ℝ W) (q : Seminorm ℝ W) (hq_cont : Continuous q)
    (hq_ge : ∀ y, p y ≤ q y)
    (f : ℕ → (W →L[ℝ] ℝ)) (c : ℕ → ℝ) (hc_nn : ∀ n, 0 ≤ c n)
    (hc_sum : Summable c) (hf_bound : ∀ n y, ‖f n y‖ ≤ q y)
    (hp_bound : ∀ y, p y ≤ ∑' n, ‖f n y‖ * c n)
    (L : V →L[ℝ] W) :
    ∃ (q' : Seminorm ℝ V), Continuous q' ∧ (∀ x, (p.comp L.toLinearMap) x ≤ q' x) ∧
      ∃ (f' : ℕ → (V →L[ℝ] ℝ)) (c' : ℕ → ℝ),
        (∀ n, 0 ≤ c' n) ∧ Summable c' ∧
        (∀ n x, ‖f' n x‖ ≤ q' x) ∧
        (∀ x, (p.comp L.toLinearMap) x ≤ ∑' n, ‖f' n x‖ * c' n) :=
  ⟨q.comp L.toLinearMap, hq_cont.comp L.continuous, fun x => hq_ge (L x),
   fun n => (f n).comp L, c, hc_nn, hc_sum,
   fun n x => by simp only [Seminorm.comp_apply, ContinuousLinearMap.comp_apply]; exact hf_bound n (L x),
   fun x => by simp only [Seminorm.comp_apply, ContinuousLinearMap.comp_apply]; exact hp_bound (L x)⟩

/-- A finite sum of seminorms, each having a nuclear decomposition, itself has a nuclear
    decomposition. This is proved by induction on the finite set, using
    nuclear_sum_decomposition at each step. -/
private theorem nuclear_finset_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V]
    {ι : Type*} (F : Finset ι) (p : ι → Seminorm ℝ V)
    (h_nuclear : ∀ i ∈ F, ∃ (q : Seminorm ℝ V), Continuous q ∧ (∀ x, p i x ≤ q x) ∧
      ∃ (f : ℕ → (V →L[ℝ] ℝ)) (c : ℕ → ℝ),
        (∀ n, 0 ≤ c n) ∧ Summable c ∧
        (∀ n x, ‖f n x‖ ≤ q x) ∧ (∀ x, p i x ≤ ∑' n, ‖f n x‖ * c n)) :
    ∃ (q : Seminorm ℝ V), Continuous q ∧ (∀ x, (F.sum p) x ≤ q x) ∧
      ∃ (f : ℕ → (V →L[ℝ] ℝ)) (c : ℕ → ℝ),
        (∀ n, 0 ≤ c n) ∧ Summable c ∧
        (∀ n x, ‖f n x‖ ≤ q x) ∧ (∀ x, (F.sum p) x ≤ ∑' n, ‖f n x‖ * c n) := by
  induction F using Finset.cons_induction with
  | empty =>
    -- Empty sum = 0, use zero decomposition
    refine ⟨0, continuous_const, ?_, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro x; simp [Finset.sum_empty, Seminorm.zero_apply]
    · intro n; rfl
    · exact summable_zero
    · intro n x; simp
    · intro x; simp [Finset.sum_empty, Seminorm.zero_apply]
  | cons a s has ih =>
    -- Inductive step: F = {a} ∪ s
    have h_a := h_nuclear a (Finset.mem_cons_self a s)
    have h_s : ∀ i ∈ s, _ := fun i hi =>
      h_nuclear i (Finset.mem_cons.mpr (Or.inr hi))
    obtain ⟨q_s, hq_s_cont, hq_s_ge, f_s, c_s, hc_s_nn, hc_s_sum, hf_s_bound, hp_s_bound⟩ :=
      ih h_s
    obtain ⟨q_a, hq_a_cont, hq_a_ge, f_a, c_a, hc_a_nn, hc_a_sum, hf_a_bound, hp_a_bound⟩ := h_a
    exact nuclear_sum_decomposition (p a) (s.sum p)
      q_a hq_a_cont hq_a_ge f_a c_a hc_a_nn hc_a_sum hf_a_bound hp_a_bound
      q_s hq_s_cont hq_s_ge f_s c_s hc_s_nn hc_s_sum hf_s_bound hp_s_bound
      ((Finset.cons a s has).sum p)
      (fun x => by rw [Finset.sum_cons]; exact le_refl _)

/-- Countable products of nuclear spaces are nuclear.

    The proof strategy: given a continuous seminorm p on the product, dominate it
    by a finite sum of pullbacks of continuous seminorms on the factors (via
    product_seminorm_dominated), apply nuclearity to each factor seminorm, then
    combine the nuclear decompositions using nuclear_finset_sum. -/
theorem product_nuclear (ι : Type*) [Countable ι]
    (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalAddGroup (E i)]
    [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, NuclearSpace (E i)] : NuclearSpace (∀ i, E i) where
  nuclear_dominance p hp := by
    -- Step 1: Dominate p by finite sum of factor seminorms
    obtain ⟨F, r, hr_cont, hp_dom⟩ := product_seminorm_dominated ι E p hp
    -- Step 2: For each i ∈ F, pull back the nuclear decomposition from E i to ∀ i, E i
    -- The projection π_i : (∀ i, E i) → E i is continuous
    let π : (i : ι) → ((j : ι) → E j) →L[ℝ] E i := fun i =>
      { toFun := fun x => x i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        cont := continuous_apply i }
    -- The pulled-back seminorms: (r i).comp (π i)
    let r_pull : ι → Seminorm ℝ (∀ i, E i) := fun i => (r i).comp (π i).toLinearMap
    -- Each pulled-back seminorm has a nuclear decomposition
    have h_nuclear : ∀ i ∈ F, ∃ (q : Seminorm ℝ (∀ j, E j)),
        Continuous q ∧ (∀ x, r_pull i x ≤ q x) ∧
        ∃ (f : ℕ → ((∀ j, E j) →L[ℝ] ℝ)) (c : ℕ → ℝ),
          (∀ n, 0 ≤ c n) ∧ Summable c ∧
          (∀ n x, ‖f n x‖ ≤ q x) ∧
          (∀ x, r_pull i x ≤ ∑' n, ‖f n x‖ * c n) := by
      intro i hi
      obtain ⟨q_i, hq_cont, hq_ge, f_i, c_i, hc_nn, hc_sum, hf_bound, hr_bound⟩ :=
        NuclearSpace.nuclear_dominance (r i) (hr_cont i hi)
      exact nuclear_pullback (r i) q_i hq_cont hq_ge f_i c_i hc_nn hc_sum hf_bound hr_bound (π i)
    -- Step 3: Combine using nuclear_finset_sum
    obtain ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bound, hsum_bound⟩ :=
      nuclear_finset_sum F r_pull h_nuclear
    -- Step 4: p ≤ F.sum r_pull, so the decomposition for F.sum r_pull works for p
    refine ⟨q, hq_cont, ?_, f, c, hc_nn, hc_sum, hf_bound, ?_⟩
    · -- q ≥ p: p ≤ F.sum r_pull ≤ q
      intro x
      calc p x ≤ ∑ i ∈ F, (r i) (x i) := hp_dom x
        _ = (F.sum r_pull) x := by
            rw [finset_sum_seminorm_apply]
            exact (Finset.sum_congr rfl fun i _ => rfl).symm
        _ ≤ q x := hq_ge x
    · -- p x ≤ Σ' n, ‖f n x‖ * c n
      intro x
      calc p x ≤ ∑ i ∈ F, (r i) (x i) := hp_dom x
        _ = (F.sum r_pull) x := by
            rw [finset_sum_seminorm_apply]
            exact (Finset.sum_congr rfl fun i _ => rfl).symm
        _ ≤ ∑' n, ‖f n x‖ * c n := hsum_bound x

end NuclearSpace

/-! ### Helper: Linear Functional Continuity from Seminorm Bound -/

/-- A linear functional bounded by a continuous seminorm is continuous
    in a topological additive group.

    This is a standard result in functional analysis: if |φ(x)| ≤ p(x) where
    p is a continuous seminorm, then φ is continuous because for any ε > 0,
    the preimage φ⁻¹((-ε, ε)) contains the open ball {x | p(x) < ε} which
    is a neighborhood of 0. Continuity at 0 gives continuity everywhere
    by translation invariance (TopologicalAddGroup). -/
private lemma linearMap_continuous_of_seminorm_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (φ : E →ₗ[ℝ] ℝ) (p : Seminorm ℝ E) (hp : Continuous p)
    (hbound : ∀ x, |φ x| ≤ p x) : Continuous φ := by
  -- Continuity at 0 implies continuity for additive group homomorphisms
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  -- The seminorm ball {x | p(x) < ε} is a neighborhood of 0
  apply Eventually.mono (Seminorm.ball_mem_nhds hp hε)
  intro x hx
  simp only [dist_zero_right, Real.norm_eq_abs]
  exact lt_of_le_of_lt (hbound x) (by rwa [sub_zero] at hx)

/-! ### Nuclear Fréchet Space Presentation -/

/-- A nuclear Fréchet space presented as a sequence of seminorms with nuclear steps.
    This is the most practical formulation for QFT applications.

    The space E comes equipped with a countable family of seminorms (pₙ)
    that define its topology, and for each n the "identity" from (E, pₙ₊₁)
    to (E, pₙ) admits a nuclear factorization: there exist linear functionals φₖ
    bounded by pₙ₊₁ and summable coefficients cₖ with pₙ(x) ≤ Σₖ |φₖ(x)| · cₖ.

    For Schwartz space, the pₙ are the Schwartz seminorms involving
    polynomial weights and derivatives.

    The `instIsTopologicalAddGroup` field ensures the topology is compatible
    with the additive group structure, which is needed for continuous linear
    functionals to be well-behaved (e.g., continuity at 0 ⟹ continuity). -/
structure NuclearFrechet where
  /-- The underlying space -/
  Space : Type*
  /-- Additive group structure -/
  instAddCommGroup : AddCommGroup Space
  /-- ℝ-module structure -/
  instModule : Module ℝ Space
  /-- Topology -/
  instTopologicalSpace : TopologicalSpace Space
  /-- The topology is compatible with the additive group structure -/
  instIsTopologicalAddGroup : @IsTopologicalAddGroup Space instTopologicalSpace
    instAddCommGroup.toAddGroup
  /-- The defining family of seminorms (indexed by ℕ) -/
  seminorms : ℕ → Seminorm ℝ Space
  /-- Seminorms are increasing: pₙ ≤ pₙ₊₁ -/
  seminorms_mono : ∀ n x, seminorms n x ≤ seminorms (n + 1) x
  /-- The seminorms separate points (Hausdorff condition) -/
  separating : ∀ x, (∀ n, seminorms n x = 0) → x = 0
  /-- Each defining seminorm is continuous with respect to the topology -/
  continuous_seminorms : ∀ n,
    @Continuous Space ℝ instTopologicalSpace inferInstance (seminorms n)
  /-- Every continuous seminorm on the space is bounded by some defining seminorm
      (the defining seminorms generate the topology). -/
  seminorms_generating : ∀ (p : Seminorm ℝ Space),
    @Continuous Space ℝ instTopologicalSpace inferInstance p →
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ x, p x ≤ C * seminorms n x
  /-- Nuclear condition: for each n, pₙ is nuclearly dominated by pₙ₊₁.
      There exist linear functionals bounded by pₙ₊₁ and summable coefficients
      that provide a nuclear-type bound on pₙ.

      Note: The functionals are given as linear maps, but they are automatically
      continuous because they are bounded by the continuous seminorm pₙ₊₁. -/
  nuclear_step : ∀ (n : ℕ),
    ∃ (φ : ℕ → Space →ₗ[ℝ] ℝ) (c : ℕ → ℝ),
      (∀ k, 0 ≤ c k) ∧
      Summable c ∧
      (∀ k x, |φ k x| ≤ seminorms (n + 1) x) ∧
      (∀ x, seminorms n x ≤ ∑' k, |φ k x| * c k)

/-! ### Connection to NuclearSpace class -/

/-- A nuclear Fréchet presentation gives rise to a NuclearSpace instance.

    The key step is that any continuous seminorm p on E is bounded by some
    C * pₙ (by the generating property of the defining seminorms), and then
    the nuclear_step condition for pₙ provides the nuclear decomposition.
    We absorb the constant C into the coefficients and scale pₙ₊₁ to serve
    as the dominating seminorm q. -/
theorem NuclearFrechet.toNuclearSpace (NF : NuclearFrechet) :
    @NuclearSpace NF.Space NF.instAddCommGroup NF.instModule NF.instTopologicalSpace := by
  letI := NF.instAddCommGroup
  letI := NF.instModule
  letI := NF.instTopologicalSpace
  letI := NF.instIsTopologicalAddGroup
  constructor
  intro p hp
  -- Step 1: p ≤ C * pₙ for some n, C > 0
  obtain ⟨n, C, hC, hpbound⟩ := NF.seminorms_generating p hp
  -- Step 2: pₙ has nuclear decomposition from pₙ₊₁
  obtain ⟨φ, c, hc_nn, hc_sum, hφ_bound, hpn_bound⟩ := NF.nuclear_step n
  -- Step 3: q = M * pₙ₊₁ where M = max(1, C) ≥ 1, absorbing the constant
  set M := max 1 C with hM_def
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_left 1 C)
  have hM_ge_one : (1 : ℝ) ≤ M := le_max_left 1 C
  have hM_ge_C : C ≤ M := le_max_right 1 C
  -- Construct q as M • pₙ₊₁
  let M_nn : ℝ≥0 := ⟨M, le_of_lt hM_pos⟩
  refine ⟨M_nn • NF.seminorms (n + 1), ?_, ?_, ?_⟩
  -- q is continuous: M * pₙ₊₁ is continuous since pₙ₊₁ is
  · suffices h : Continuous (fun x => M * NF.seminorms (n + 1) x) by
      have : (⇑(M_nn • NF.seminorms (n + 1)) : NF.Space → ℝ) =
          fun x => M * NF.seminorms (n + 1) x := by
        ext x; simp [M_nn, NNReal.smul_def]
      rwa [show @Continuous NF.Space ℝ NF.instTopologicalSpace _ ⇑(M_nn • NF.seminorms (n + 1)) ↔
        @Continuous NF.Space ℝ NF.instTopologicalSpace _ (fun x => M * NF.seminorms (n + 1) x)
        from Iff.intro (fun h => by rwa [← this]) (fun h => by rwa [this])]
    exact continuous_const.mul (NF.continuous_seminorms (n + 1))
  -- q ≥ p: p ≤ C * pₙ ≤ C * pₙ₊₁ ≤ M * pₙ₊₁ = q
  · intro x
    have hsmul : (M_nn • NF.seminorms (n + 1)) x = M * NF.seminorms (n + 1) x := by
      simp [M_nn, NNReal.smul_def]
    rw [hsmul]
    calc p x ≤ C * NF.seminorms n x := hpbound x
    _ ≤ C * NF.seminorms (n + 1) x :=
        mul_le_mul_of_nonneg_left (NF.seminorms_mono n x) (le_of_lt hC)
    _ ≤ M * NF.seminorms (n + 1) x :=
        mul_le_mul_of_nonneg_right hM_ge_C (apply_nonneg _ x)
  -- Nuclear decomposition: fₖ = φₖ (made continuous), c'ₖ = C * cₖ
  · -- Each φₖ is bounded by pₙ₊₁ (continuous), so φₖ is continuous
    have hcont_phi : ∀ k, @Continuous NF.Space ℝ NF.instTopologicalSpace _ (φ k) :=
      fun k => linearMap_continuous_of_seminorm_bound (φ k) (NF.seminorms (n + 1))
        (NF.continuous_seminorms (n + 1)) (hφ_bound k)
    refine ⟨fun k => ⟨φ k, hcont_phi k⟩, fun k => C * c k, ?_, ?_, ?_, ?_⟩
    -- c' ≥ 0
    · intro k; exact mul_nonneg (le_of_lt hC) (hc_nn k)
    -- Summable c': follows from Summable c
    · exact hc_sum.const_smul C
    -- ‖fₖ(x)‖ ≤ q(x): |φₖ(x)| ≤ pₙ₊₁(x) ≤ M * pₙ₊₁(x) = q(x)
    · intro k x
      have hsmul : (M_nn • NF.seminorms (n + 1)) x = M * NF.seminorms (n + 1) x := by
        simp [M_nn, NNReal.smul_def]
      simp only [ContinuousLinearMap.coe_mk', Real.norm_eq_abs]
      rw [hsmul]
      calc |φ k x| ≤ NF.seminorms (n + 1) x := hφ_bound k x
      _ ≤ M * NF.seminorms (n + 1) x :=
          le_mul_of_one_le_left (apply_nonneg _ x) hM_ge_one
    -- p(x) ≤ Σ ‖fₖ(x)‖ * c'ₖ: absorb C into the tsum
    · intro x
      have hpn := hpn_bound x
      simp only [ContinuousLinearMap.coe_mk', Real.norm_eq_abs]
      calc p x ≤ C * NF.seminorms n x := hpbound x
      _ ≤ C * (∑' k, |φ k x| * c k) :=
          mul_le_mul_of_nonneg_left hpn (le_of_lt hC)
      _ = ∑' k, C * (|φ k x| * c k) := by rw [← tsum_mul_left]
      _ = ∑' k, |φ k x| * (C * c k) := by congr 1; ext k; ring

end
