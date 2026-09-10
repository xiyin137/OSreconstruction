/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.UniformSpace.Completion
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.Specification.Wightman
import OSReconstruction.Wightman.SchwartzTensorProduct




































set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped SchwartzMap
open Topology

variable (d : ℕ) [NeZero d]

-- Many inner product theorems only use d : ℕ, not [NeZero d].
-- Suppress the auto-inclusion warning for these infrastructure lemmas.
set_option linter.unusedSectionVars false














namespace BorchersSequence

variable {d : ℕ}

instance : Zero (BorchersSequence d) where
  zero := ⟨fun _ => 0, 0, fun _ _ => rfl⟩

instance : Add (BorchersSequence d) where
  add F G := ⟨fun n => F.funcs n + G.funcs n, max F.bound G.bound,
    fun n hn => by simp [F.bound_spec n (by omega), G.bound_spec n (by omega)]⟩

instance : Neg (BorchersSequence d) where
  neg F := ⟨fun n => -(F.funcs n), F.bound, fun n hn => by simp [F.bound_spec n hn]⟩

instance : SMul ℂ (BorchersSequence d) where
  smul c F := ⟨fun n => c • (F.funcs n), F.bound, fun n hn => by simp [F.bound_spec n hn]⟩

instance : Sub (BorchersSequence d) where
  sub F G := ⟨fun n => F.funcs n - G.funcs n, max F.bound G.bound,
    fun n hn => by simp [F.bound_spec n (by omega), G.bound_spec n (by omega)]⟩

@[simp] theorem zero_funcs (n : ℕ) : (0 : BorchersSequence d).funcs n = 0 := rfl
@[simp] theorem add_funcs (F G : BorchersSequence d) (n : ℕ) :
    (F + G).funcs n = F.funcs n + G.funcs n := rfl
@[simp] theorem neg_funcs (F : BorchersSequence d) (n : ℕ) :
    (-F).funcs n = -(F.funcs n) := rfl
@[simp] theorem smul_funcs (c : ℂ) (F : BorchersSequence d) (n : ℕ) :
    (c • F).funcs n = c • (F.funcs n) := rfl
@[simp] theorem sub_funcs (F G : BorchersSequence d) (n : ℕ) :
    (F - G).funcs n = F.funcs n - G.funcs n := rfl
@[simp] theorem smul_bound (c : ℂ) (F : BorchersSequence d) : (c • F).bound = F.bound := rfl
@[simp] theorem neg_bound (F : BorchersSequence d) : (-F).bound = F.bound := rfl
@[simp] theorem sub_bound (F G : BorchersSequence d) :
    (F - G).bound = max F.bound G.bound := rfl
@[simp] theorem add_bound (F G : BorchersSequence d) :
    (F + G).bound = max F.bound G.bound := rfl

/-- Linear combination of Borchers sequences over a Finset.
    Defined componentwise via `Finset.sum` on `SchwartzNPoint` (which has `AddCommMonoid`).
    Avoids the need for a full `AddCommMonoid` instance on `BorchersSequence`. -/
noncomputable def linearCombo {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (G : ι → BorchersSequence d) : BorchersSequence d where
  funcs n := ∑ i ∈ s, c i • (G i).funcs n
  bound := s.sup (fun i => (G i).bound)
  bound_spec n hn := by
    apply Finset.sum_eq_zero
    intro i hi
    have hbi : (G i).bound < n := by
      calc (G i).bound ≤ s.sup (fun i => (G i).bound) :=
            Finset.le_sup (f := fun i => (G i).bound) hi
        _ < n := hn
    simp [(G i).bound_spec n hbi]

@[simp] theorem linearCombo_funcs {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (G : ι → BorchersSequence d) (n : ℕ) :
    (linearCombo s c G).funcs n = ∑ i ∈ s, c i • (G i).funcs n := rfl

/-- The Borchers sequence concentrated in degree `n` with component `f`. -/
def single (n : ℕ) (f : SchwartzNPoint d n) : BorchersSequence d where
  funcs m := by
    by_cases h : m = n
    · subst h
      exact f
    · exact 0
  bound := n
  bound_spec m hm := by
    by_cases h : m = n
    · omega
    · simp [h]

@[simp] theorem single_bound (n : ℕ) (f : SchwartzNPoint d n) :
    (single n f).bound = n := rfl

@[simp] theorem single_funcs_eq (n : ℕ) (f : SchwartzNPoint d n) :
    (single n f).funcs n = f := by
  simp [single]

@[simp] theorem single_funcs_ne {n m : ℕ} (h : m ≠ n) (f : SchwartzNPoint d n) :
    (single n f).funcs m = 0 := by
  simp [single, h]

end BorchersSequence










/-- The standard inner product equals the N-bounded version with the natural bounds. -/
theorem WightmanInnerProduct_eq_N (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W F G = WightmanInnerProductN d W F G (F.bound + 1) (G.bound + 1) :=
  rfl

/-- Extending the second summation range doesn't change the inner product
    when W is ℂ-linear and the extra terms have zero Schwartz functions. -/
theorem WightmanInnerProductN_extend_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₂ : G.bound + 1 ≤ N₂) :
    WightmanInnerProductN d W F G N₁ N₂ = WightmanInnerProductN d W F G N₁ (G.bound + 1) := by
  unfold WightmanInnerProductN
  apply Finset.sum_congr rfl
  intro n _
  -- Goal: ∑ m ∈ range N₂, ... = ∑ m ∈ range (G.bound + 1), ...
  -- sum_subset gives: small ⊆ big → (extra = 0) → ∑ small = ∑ big
  symm
  apply Finset.sum_subset (Finset.range_mono hN₂)
  intro m hm₂ hm₁
  have hm : G.bound < m := by
    simp only [Finset.mem_range] at hm₁ hm₂; omega
  rw [G.bound_spec m hm, SchwartzMap.conjTensorProduct_zero_right, (hlin _).map_zero]

/-- Extending the first summation range doesn't change the inner product. -/
theorem WightmanInnerProductN_extend_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) :
    WightmanInnerProductN d W F G N₁ N₂ = WightmanInnerProductN d W F G (F.bound + 1) N₂ := by
  unfold WightmanInnerProductN
  -- Goal: ∑ n ∈ range N₁, (∑ m ...) = ∑ n ∈ range (F.bound+1), (∑ m ...)
  symm
  apply Finset.sum_subset (Finset.range_mono hN₁)
  intro n hn₂ hn₁
  have hn : F.bound < n := by
    simp only [Finset.mem_range] at hn₁ hn₂; omega
  -- The inner sum is zero because F.funcs n = 0
  apply Finset.sum_eq_zero
  intro m _
  rw [F.bound_spec n hn, SchwartzMap.conjTensorProduct_zero_left, (hlin _).map_zero]

/-- Key lemma: the inner product can be computed using any sufficiently large bounds. -/
theorem WightmanInnerProduct_eq_extended (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) (hN₂ : G.bound + 1 ≤ N₂) :
    WightmanInnerProduct d W F G = WightmanInnerProductN d W F G N₁ N₂ := by
  rw [WightmanInnerProduct_eq_N,
    ← WightmanInnerProductN_extend_right d W hlin F G (F.bound + 1) N₂ hN₂,
    ← WightmanInnerProductN_extend_left d W hlin F G N₁ N₂ hN₁]

/-- Against concentrated Borchers vectors, the Wightman inner product reduces
to the single tensor term in the corresponding degree. -/
theorem WightmanInnerProduct_single_single (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    WightmanInnerProduct d W (BorchersSequence.single n f) (BorchersSequence.single m g) =
      W (n + m) (f.conjTensorProduct g) := by
  unfold WightmanInnerProduct
  rw [BorchersSequence.single_bound, BorchersSequence.single_bound, Finset.sum_range_succ]
  have hleft :
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range (m + 1),
          W (i + j)
            (((BorchersSequence.single n f).funcs i).conjTensorProduct
              ((BorchersSequence.single m g).funcs j)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
    apply Finset.sum_eq_zero
    intro j hj
    rw [BorchersSequence.single_funcs_ne hi_ne,
      SchwartzMap.conjTensorProduct_zero_left, (hlin _).map_zero]
  rw [hleft, zero_add, BorchersSequence.single_funcs_eq, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        W (n + j)
          (f.conjTensorProduct ((BorchersSequence.single m g).funcs j)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne,
      SchwartzMap.conjTensorProduct_zero_right, (hlin _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]



/-- The inner product is additive in the second argument. -/
theorem WightmanInnerProduct_add_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G₁ G₂ : BorchersSequence d) :
    WightmanInnerProduct d W F (G₁ + G₂) =
    WightmanInnerProduct d W F G₁ + WightmanInnerProduct d W F G₂ := by
  -- Use a common bound for all three inner products
  have hN₁ : F.bound + 1 ≤ F.bound + 1 := le_refl _
  have hN₂_sum : (G₁ + G₂).bound + 1 ≤ max G₁.bound G₂.bound + 1 := le_refl _
  have hN₂_1 : G₁.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₂_2 : G₂.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  rw [WightmanInnerProduct_eq_extended d W hlin F (G₁ + G₂)
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_sum,
      WightmanInnerProduct_eq_extended d W hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_1,
      WightmanInnerProduct_eq_extended d W hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_2]
  -- Now all three sums use the same range, so we can combine pointwise
  simp only [WightmanInnerProductN, BorchersSequence.add_funcs,
    SchwartzMap.conjTensorProduct_add_right, (hlin _).map_add]
  rw [← Finset.sum_add_distrib]
  congr 1; ext n
  rw [← Finset.sum_add_distrib]

/-- The inner product is additive in the first argument (with conjugation). -/
theorem WightmanInnerProduct_add_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F₁ F₂ G : BorchersSequence d) :
    WightmanInnerProduct d W (F₁ + F₂) G =
    WightmanInnerProduct d W F₁ G + WightmanInnerProduct d W F₂ G := by
  have hN₁_sum : (F₁ + F₂).bound + 1 ≤ max F₁.bound F₂.bound + 1 := le_refl _
  have hN₁_1 : F₁.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₁_2 : F₂.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  have hN₂ : G.bound + 1 ≤ G.bound + 1 := le_refl _
  rw [WightmanInnerProduct_eq_extended d W hlin (F₁ + F₂) G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_sum hN₂,
      WightmanInnerProduct_eq_extended d W hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_1 hN₂,
      WightmanInnerProduct_eq_extended d W hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_2 hN₂]
  simp only [WightmanInnerProductN, BorchersSequence.add_funcs,
    SchwartzMap.conjTensorProduct_add_left, (hlin _).map_add]
  rw [← Finset.sum_add_distrib]
  congr 1; ext n
  rw [← Finset.sum_add_distrib]

/-- The inner product scales linearly in the second argument. -/
theorem WightmanInnerProduct_smul_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (c : ℂ) (F G : BorchersSequence d) :
    WightmanInnerProduct d W F (c • G) = c * WightmanInnerProduct d W F G := by
  simp only [WightmanInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound,
    SchwartzMap.conjTensorProduct_smul_right, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]; congr 1; ext n
  rw [Finset.mul_sum]

/-- Conjugate linearity of the inner product in the first argument:
    ⟨c·F, G⟩ = c̄·⟨F, G⟩ -/
theorem WightmanInnerProduct_smul_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (c : ℂ) (F G : BorchersSequence d) :
    WightmanInnerProduct d W (c • F) G = starRingEnd ℂ c * WightmanInnerProduct d W F G := by
  simp only [WightmanInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound,
    SchwartzMap.conjTensorProduct_smul_left, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]; congr 1; ext n
  rw [Finset.mul_sum]



-- Note: renamed from `IsPositiveDefinite` to avoid collision with
-- `Bochner.PositiveDefinite.IsPositiveDefinite` from the HilleYosida dependency.



namespace WightmanFunctionsCore

variable {d : ℕ} [NeZero d]

/-- Add locality and clustering to the same core Wightman family. -/
def toWightmanFunctions (Wcore : WightmanFunctionsCore d)
    (hlocal : IsAdjacentLocallyCommutativeWeak d Wcore.W)
    (hcluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖Wcore.W (n + m) (f.tensorProduct g_a) - Wcore.W n f * Wcore.W m g‖ < ε) :
    WightmanFunctions d where
  W := Wcore.W
  linear := Wcore.linear
  tempered := Wcore.tempered
  normalized := Wcore.normalized
  translation_invariant := Wcore.translation_invariant
  lorentz_covariant := Wcore.lorentz_covariant
  spectrum_condition := Wcore.spectrum_condition
  spectral_support := Wcore.spectral_support
  locally_commutative := hlocal
  positive_definite := Wcore.positive_definite
  hermitian := Wcore.hermitian
  cluster := hcluster
  spectrum_condition_compact_subset := by
    intro n K hK hsub
    exact (Wcore.spectrum_condition n).choose_spec.2.1 K hK hsub

end WightmanFunctionsCore


/-- Forward-tube growth input needed for the corrected `R -> E` direction.

    This is intentionally a separate proposition, not part of the core
    `WightmanFunctions` structure: the existing Wightman record captures the
    standard distributional axioms, while the Euclidean zero-diagonal pairing
    additionally needs explicit control of coincidence singularities for the
    Wick-rotated kernel.

    The expected source is the usual Vladimirov-type tube estimate together
    with Euclidean symmetry/translation arguments. Keeping it separate avoids
    strengthening every `WightmanFunctions` constructor globally when only the
    `R -> E` bridge needs it. -/
def HasForwardTubeGrowth {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) : Prop :=
  -- Weighted bound: for all n, the product of ‖W_analytic(wick(x))‖ with a power of
  -- infDist(x, CoincidenceLocus) is at most polynomial. This is the Vladimirov-Tillmann
  -- boundary-singularity control transferred to the Euclidean setting.
  -- For n ≤ 1 (empty CoincidenceLocus) the infDist factor is 0, so the bound is
  -- vacuously true; the n ≤ 1 integrability is handled separately.
  ∀ (n : ℕ),
    ∃ (C_bd : ℝ) (N q : ℕ), C_bd > 0 ∧
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n →
          ‖(Wfn.spectrum_condition n).choose (fun k => wickRotatePoint (x k))‖ *
            Metric.infDist x
              { y : Fin n → Fin (d + 1) → ℝ |
                ∃ i j : Fin n, i ≠ j ∧ y i = y j } ^ (q + 1) ≤
                  C_bd * (1 + ‖x‖) ^ N

/-- Dependent type transport for Wightman functions: if k₁ = k₂ and two test functions
    have the same pointwise values (modulo the Fin.cast reindexing), then W gives the same value.
    This handles the n+m ↔ m+n identification. -/
theorem W_eq_of_cast {d : ℕ}
    (W : (k : ℕ) → SchwartzNPoint d k → ℂ)
    (k₁ k₂ : ℕ) (hk : k₁ = k₂)
    (f : SchwartzNPoint d k₁) (g : SchwartzNPoint d k₂)
    (hfg : ∀ x, f x = g (fun i => x (Fin.cast hk.symm i))) :
    W k₁ f = W k₂ g := by
  subst hk; congr 1; ext x; exact hfg x

/-- Key reversal identity for Hermiticity:
    (f.conjTP g) x = (g.conjTP f).borchersConj (x ∘ Fin.cast ...)

    Both sides reduce to conj(f(A)) * g(B) (after mul_comm), where A, B are
    reindexings of x. The coordinate arithmetic is verified by omega. -/
private theorem conjTP_eq_borchersConj_conjTP {d n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    (f.conjTensorProduct g) x =
      ((g.conjTensorProduct f).borchersConj)
        (fun i => x (Fin.cast (Nat.add_comm n m).symm i)) := by
  simp only [SchwartzMap.borchersConj_apply, SchwartzMap.conjTensorProduct_apply,
    map_mul, starRingEnd_self_apply]
  rw [mul_comm]
  -- Both sides: g(arg_g) * conj(f(arg_f)). Show arguments match.
  congr 1
  · -- g factor: splitLast n m x = fun k => splitFirst m n (z ∘ rev) (rev k)
    congr 1; ext k; simp only [splitFirst, splitLast]
    congr 1; ext; simp [Fin.val_natAdd, Fin.val_rev, Fin.val_castAdd, Fin.val_cast]; omega
  · -- conj(f) factor: peel starRingEnd then f
    congr 1; congr 1; ext k; simp only [splitFirst, splitLast]
    congr 1; ext; simp [Fin.val_natAdd, Fin.val_rev, Fin.val_castAdd, Fin.val_cast]; omega

/-- The Wightman inner product satisfies Hermiticity: ⟨F, G⟩ = conj(⟨G, F⟩).

    This structure-free form only assumes the distribution-level Hermiticity
    axiom for the underlying `n`-point family. It is useful before a full
    `WightmanFunctions` structure is available. -/
theorem WightmanInnerProduct_hermitian_of {d : ℕ} [NeZero d]
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        W n g = starRingEnd ℂ (W n f))
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W F G = starRingEnd ℂ (WightmanInnerProduct d W G F) := by
  simp only [WightmanInnerProduct, map_sum]
  rw [Finset.sum_comm]
  congr 1; ext n; congr 1; ext m
  rw [← hherm (n + m) ((G.funcs n).conjTensorProduct (F.funcs m))
    (((G.funcs n).conjTensorProduct (F.funcs m)).borchersConj) (fun _ => rfl)]
  exact W_eq_of_cast W (m + n) (n + m) (Nat.add_comm m n)
    ((F.funcs m).conjTensorProduct (G.funcs n))
    (((G.funcs n).conjTensorProduct (F.funcs m)).borchersConj)
    (fun x => conjTP_eq_borchersConj_conjTP (F.funcs m) (G.funcs n) x)

/-- If at² + bt ≥ 0 for all real t, with a ≥ 0, then b = 0.
    This is the key algebraic lemma for the Cauchy-Schwarz argument. -/
theorem quadratic_nonneg_linear_zero
    (a b : ℝ) (ha : 0 ≤ a) (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t) :
    b = 0 := by
  by_cases ha0 : a = 0
  · have h1 := h 1; have h2 := h (-1); simp [ha0] at h1 h2; linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h4a_pos : (0 : ℝ) < 4 * a := by linarith
    have key := h (-b / (2 * a))
    have calc_eq : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) = -(b ^ 2) / (4 * a) := by
      field_simp; ring
    rw [calc_eq] at key
    have hbsq_nonpos : b ^ 2 ≤ 0 := by
      rwa [le_div_iff₀ h4a_pos, zero_mul, neg_nonneg] at key
    exact sq_eq_zero_iff.mp (le_antisymm hbsq_nonpos (sq_nonneg b))

/-- A nonnegative real quadratic has nonpositive discriminant, in the form
needed for semidefinite Cauchy--Schwarz estimates. -/
theorem quadratic_nonneg_sq_le
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 ≤ a + 2 * c * t + b * t ^ 2) :
    c ^ 2 ≤ a * b := by
  by_cases hb0 : b = 0
  · subst b
    have hc : c = 0 := by
      by_contra hc0
      have hbad := h (-(a + 1) / (2 * c))
      have hcalc :
          a + 2 * c * (-(a + 1) / (2 * c)) = -1 := by
        field_simp [hc0]
        ring
      simp only [zero_mul, add_zero] at hbad
      rw [hcalc] at hbad
      linarith
    simp [hc]
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hmin := h (-c / b)
    have hcalc :
        a + 2 * c * (-c / b) + b * (-c / b) ^ 2 =
          a - c ^ 2 / b := by
      field_simp [hb0]
      ring
    rw [hcalc] at hmin
    exact (div_le_iff₀ hb_pos).mp (by linarith)

/-- Quadratic expansion: ⟨X + tY, X + tY⟩.re = ⟨X,X⟩.re + 2t·Re⟨X,Y⟩ + t²·⟨Y,Y⟩.re -/
theorem WightmanInnerProduct_quadratic_re_of {d : ℕ} [NeZero d]
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        W n g = starRingEnd ℂ (W n f))
    (X Y : BorchersSequence d) (t : ℝ) :
    (WightmanInnerProduct d W (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re =
    (WightmanInnerProduct d W X X).re +
    2 * (WightmanInnerProduct d W X Y).re * t +
    (WightmanInnerProduct d W Y Y).re * t ^ 2 := by
  -- Expand using sesquilinearity + Hermiticity
  rw [WightmanInnerProduct_add_left d W hlin,
      WightmanInnerProduct_add_right d W hlin X,
      WightmanInnerProduct_add_right d W hlin ((↑t : ℂ) • Y),
      WightmanInnerProduct_smul_right d W hlin _ X,
      WightmanInnerProduct_smul_left d W hlin _ Y,
      WightmanInnerProduct_smul_left d W hlin _ Y,
      WightmanInnerProduct_smul_right d W hlin _ Y,
      WightmanInnerProduct_hermitian_of W hherm Y X]
  -- Simplify conj(↑t) = ↑t for real t, then distribute .re
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A structure-free semidefinite Cauchy--Schwarz estimate for the Wightman
pairing. The factor `2` comes from applying the real quadratic estimate to the
real and imaginary parts separately; this is sufficient for density closure
without constructing the GNS quotient prematurely. -/
theorem WightmanInnerProduct_norm_sq_le_two_mul_of {d : ℕ} [NeZero d]
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        W n g = starRingEnd ℂ (W n f))
    (hpos : ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d W F F).re)
    (F G : BorchersSequence d) :
    ‖WightmanInnerProduct d W F G‖ ^ 2 ≤
      2 * (WightmanInnerProduct d W F F).re *
        (WightmanInnerProduct d W G G).re := by
  let w := WightmanInnerProduct d W F G
  let qF := (WightmanInnerProduct d W F F).re
  let qG := (WightmanInnerProduct d W G G).re
  have hre : w.re ^ 2 ≤ qF * qG := by
    apply quadratic_nonneg_sq_le qF qG w.re
    · exact hpos F
    · exact hpos G
    · intro t
      rw [show qF + 2 * w.re * t + qG * t ^ 2 =
        (WightmanInnerProduct d W
          (F + (↑t : ℂ) • G) (F + (↑t : ℂ) • G)).re from by
            exact (WightmanInnerProduct_quadratic_re_of W hlin hherm F G t).symm]
      exact hpos _
  have hqGI :
      (WightmanInnerProduct d W (Complex.I • G) (Complex.I • G)).re = qG := by
    rw [WightmanInnerProduct_smul_left d W hlin,
      WightmanInnerProduct_smul_right d W hlin]
    simp [qG]
  have hpairI :
      (WightmanInnerProduct d W F (Complex.I • G)).re = -w.im := by
    rw [WightmanInnerProduct_smul_right d W hlin]
    simp [w, Complex.mul_re]
  have him : w.im ^ 2 ≤ qF * qG := by
    have hbound :
        (-w.im) ^ 2 ≤ qF * qG := by
      apply quadratic_nonneg_sq_le qF qG (-w.im) (hpos F) (hpos G)
      intro t
      rw [← hqGI, ← hpairI]
      rw [show qF +
          2 * (WightmanInnerProduct d W F (Complex.I • G)).re * t +
          (WightmanInnerProduct d W (Complex.I • G) (Complex.I • G)).re * t ^ 2 =
        (WightmanInnerProduct d W
          (F + (↑t : ℂ) • (Complex.I • G))
          (F + (↑t : ℂ) • (Complex.I • G))).re from by
            exact (WightmanInnerProduct_quadratic_re_of W hlin hherm
              F (Complex.I • G) t).symm]
      exact hpos _
    nlinarith
  have hnorm :
      ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hnorm]
  nlinarith





namespace Reconstruction

variable {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)

/-- The vacuum Borchers sequence: f_0 = 1 (constant function), f_n = 0 for n ≥ 1.
    The vacuum is the unit of the Borchers algebra. Its inner product with
    φ(f₁)···φ(fₙ)Ω gives W_n(f₁ ⊗ ··· ⊗ fₙ). -/
def vacuumSequence : BorchersSequence d where
  funcs := fun n => match n with
    | 0 => {
        toFun := fun _ => 1
        smooth' := contDiff_const
        decay' := by
          intro k n
          use 1
          intro x
          rw [show x = 0 from Subsingleton.elim x 0, norm_zero]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp only [pow_zero, one_mul]
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · rw [norm_iteratedFDeriv_zero]; simp
            · simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ)
                (Nat.pos_iff_ne_zero.mp hn) (1 : ℂ) (E := NPointDomain d 0)]
          · simp [zero_pow (Nat.pos_iff_ne_zero.mp hk)]
      }
    | _ + 1 => 0
  bound := 1
  bound_spec := fun n hn => by
    match n with
    | 0 => omega
    | k + 1 => rfl

/-- The field operator action on Borchers sequences.
    For a test function f ∈ S(ℝ^{d+1}), this creates the sequence (φ(f)F) where:
    - (φ(f)F)₀ = 0
    - (φ(f)F)ₙ₊₁ = f ⊗ Fₙ for n ≥ 0 (prepend f as the first argument)

    The (n+1)-th component is the tensor product of f (as a 1-point function) with
    the n-th component of F, giving an (n+1)-point test function:
      (φ(f)F)_{n+1}(x₁,...,x_{n+1}) = f(x₁) · Fₙ(x₂,...,x_{n+1}) -/
private def fieldOperatorFuncs (f : SchwartzSpacetime d)
    (g : (n : ℕ) → SchwartzNPoint d n) : (n : ℕ) → SchwartzNPoint d n
  | 0 => 0
  | k + 1 => SchwartzMap.prependField f (g k)

def fieldOperatorAction (f : SchwartzSpacetime d) (F : BorchersSequence d) :
    BorchersSequence d where
  funcs := fieldOperatorFuncs f F.funcs
  bound := F.bound + 1
  bound_spec := fun n hn => by
    cases n with
    | zero => omega
    | succ k =>
      -- Goal reduces to: prependField f (F.funcs k) = 0
      -- Since F.bound + 1 < k + 1, we have F.bound < k, so F.funcs k = 0
      simp only [fieldOperatorFuncs, F.bound_spec k (by omega),
        SchwartzMap.prependField_zero_right]

@[simp]
theorem fieldOperatorAction_funcs_zero (f : SchwartzSpacetime d) (F : BorchersSequence d) :
    (fieldOperatorAction f F).funcs 0 = 0 := rfl

@[simp]
theorem fieldOperatorAction_funcs_succ (f : SchwartzSpacetime d) (F : BorchersSequence d) (k : ℕ) :
    (fieldOperatorAction f F).funcs (k + 1) = SchwartzMap.prependField f (F.funcs k) := rfl

@[simp]
theorem fieldOperatorAction_bound (f : SchwartzSpacetime d) (F : BorchersSequence d) :
    (fieldOperatorAction f F).bound = F.bound + 1 := rfl

end Reconstruction



-- `wightman_reconstruction` and `wightman_uniqueness` moved to Reconstruction/Main.lean
-- (proved via GNS construction in GNSHilbertSpace.lean)










































/-- The OS-I ordered positive-time region: `0 < x₁⁰ < ... < xₙ⁰`.

    This is the support surface used in the positivity axiom `E2`, matching the
    test-function space `S^<_{+}` in OS I. -/
def OrderedPositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, 0 < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0 }

/-- The time-reflected ordered region: all times are negative and strictly decrease. -/
def OrderedNegativeTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 < 0 ∧ ∀ j : Fin n, i < j → x j 0 < x i 0 }

/-- The coincidence locus where at least two Euclidean arguments coincide. -/
def CoincidenceLocus (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∃ i j : Fin n, i ≠ j ∧ x i = x j }

/-- The one-point coincidence locus is empty. -/
theorem coincidenceLocus_one_eq_empty {d : ℕ} :
    CoincidenceLocus d 1 = ∅ := by
  ext x
  simp [CoincidenceLocus]

theorem not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion
    {d n : ℕ} {x : NPointDomain d n}
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    x ∉ CoincidenceLocus d n := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
  · have htime : x i 0 < x j 0 := (hx i).2 j hij_lt
    have hEq0 : x i 0 = x j 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq
    exact (lt_irrefl (x i 0)) (hEq0 ▸ htime)
  · have htime : x j 0 < x i 0 := (hx j).2 i hij_gt
    have hEq0 : x j 0 = x i 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq.symm
    exact (lt_irrefl (x j 0)) (hEq0 ▸ htime)

theorem not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion
    {d n : ℕ} {x : NPointDomain d n}
    (hx : x ∈ OrderedNegativeTimeRegion d n) :
    x ∉ CoincidenceLocus d n := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
  · have htime : x j 0 < x i 0 := (hx i).2 j hij_lt
    have hEq0 : x i 0 = x j 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq
    exact (lt_irrefl (x j 0)) (hEq0 ▸ htime)
  · have htime : x i 0 < x j 0 := (hx j).2 i hij_gt
    have hEq0 : x j 0 = x i 0 := by
      simpa using congrArg (fun y : SpacetimeDim d => y 0) hijEq.symm
    exact (lt_irrefl (x i 0)) (hEq0 ▸ htime)

/-- A Schwartz test function vanishes to infinite order on the coincidence locus
    if every iterated Fréchet derivative vanishes at every coincident configuration.

    This is the current formal stand-in for the OS-I test space `°S`: in finite
    dimensions, vanishing of all iterated Fréchet derivatives is the coordinate-free
    formulation of “vanishes with all partial derivatives on every diagonal.” -/
def VanishesToInfiniteOrderOnCoincidence {d n : ℕ} (f : SchwartzNPoint d n) : Prop :=
  ∀ k : ℕ, ∀ x : NPointDomain d n, x ∈ CoincidenceLocus d n →
    iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ) x = 0

/-- Every one-point Schwartz test function is automatically zero-diagonal,
since there are no coincidence configurations. -/
theorem VanishesToInfiniteOrderOnCoincidence.one {d : ℕ}
    (f : SchwartzNPoint d 1) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hx
  simp [coincidenceLocus_one_eq_empty (d := d)] at hx

theorem VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
    {d n : ℕ} (f : SchwartzNPoint d n)
    (hdisj : Disjoint (tsupport (f : NPointDomain d n → ℂ)) (CoincidenceLocus d n)) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hxcoin
  have hx_not_tsupport : x ∉ tsupport (f : NPointDomain d n → ℂ) := by
    intro hxt
    exact Set.disjoint_left.mp hdisj hxt hxcoin
  have hx_not_support :
      x ∉ Function.support (iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ)) := by
    intro hx
    exact hx_not_tsupport
      ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) (f := ⇑f)) hx)
  by_contra hx_nonzero
  exact hx_not_support (by simpa [Function.mem_support, hx_nonzero])

omit [NeZero d] in
private def coincidenceCollapse {n : ℕ} (i j : Fin n) (x : NPointDomain d n) :
    NPointDomain d n :=
  fun k => if k = i ∨ k = j then midpoint ℝ (x i) (x j) else x k

omit [NeZero d] in
private theorem coincidenceCollapse_mem_CoincidenceLocus {n : ℕ}
    (x : NPointDomain d n) (i j : Fin n) (hij : i ≠ j) :
    coincidenceCollapse (d := d) i j x ∈ CoincidenceLocus d n := by
  refine ⟨i, j, hij, ?_⟩
  ext μ
  simp [coincidenceCollapse, hij]

omit [NeZero d] in
private theorem norm_sub_coincidenceCollapse_le_pairDifference {n : ℕ}
    (x : NPointDomain d n) (i j : Fin n) (hij : i ≠ j) :
    ‖x - coincidenceCollapse (d := d) i j x‖ ≤ ‖x i - x j‖ := by
  change ↑(Finset.univ.sup fun k => ‖(x - coincidenceCollapse (d := d) i j x) k‖₊) ≤ ‖x i - x j‖
  have hdistNN :
      Finset.univ.sup
          (fun k => ‖(x - coincidenceCollapse (d := d) i j x) k‖₊) ≤
        ‖x i - x j‖₊ := by
    refine Finset.sup_le_iff.mpr ?_
    intro k hk
    by_cases hki : k = i
    · subst k
      have hkreal :
          ‖(x - coincidenceCollapse (d := d) i j x) i‖ ≤ ‖x i - x j‖ := by
        calc
          ‖(x - coincidenceCollapse (d := d) i j x) i‖ =
              ‖x i - midpoint ℝ (x i) (x j)‖ := by
                simp [coincidenceCollapse, hij]
          _ = ‖(⅟ (2 : ℝ)) • (x i - x j)‖ := by rw [left_sub_midpoint]
          _ = ‖(⅟ (2 : ℝ))‖ * ‖x i - x j‖ := norm_smul _ _
          _ ≤ 1 * ‖x i - x j‖ := by
              gcongr
              norm_num
          _ = ‖x i - x j‖ := by ring
      exact_mod_cast hkreal
    · by_cases hkj : k = j
      · subst k
        have hkreal :
            ‖(x - coincidenceCollapse (d := d) i j x) j‖ ≤ ‖x i - x j‖ := by
          calc
            ‖(x - coincidenceCollapse (d := d) i j x) j‖ =
                ‖x j - midpoint ℝ (x i) (x j)‖ := by
                  simp [coincidenceCollapse, hki]
            _ = ‖(⅟ (2 : ℝ)) • (x j - x i)‖ := by rw [right_sub_midpoint]
            _ = ‖(⅟ (2 : ℝ))‖ * ‖x j - x i‖ := norm_smul _ _
            _ ≤ 1 * ‖x j - x i‖ := by
                gcongr
                norm_num
            _ = ‖x i - x j‖ := by rw [norm_sub_rev, one_mul]
        exact_mod_cast hkreal
      · simp [coincidenceCollapse, hki, hkj]
  exact_mod_cast hdistNN

omit [NeZero d] in
private def coincidenceCopy {n : ℕ} (src dst : Fin n) (x : NPointDomain d n) :
    NPointDomain d n :=
  fun k => if k = dst then x src else x k

omit [NeZero d] in
private theorem coincidenceCopy_mem_CoincidenceLocus {n : ℕ}
    (x : NPointDomain d n) (src dst : Fin n) (hsrcdst : src ≠ dst) :
    coincidenceCopy (d := d) src dst x ∈ CoincidenceLocus d n := by
  refine ⟨src, dst, hsrcdst, ?_⟩
  ext μ
  simp [coincidenceCopy, hsrcdst]

omit [NeZero d] in
private theorem norm_sub_coincidenceCopy_eq_pairDifference {n : ℕ}
    (x : NPointDomain d n) (src dst : Fin n) :
    ‖x - coincidenceCopy (d := d) src dst x‖ = ‖x src - x dst‖ := by
  change ↑(Finset.univ.sup
      (fun k => ‖(x - coincidenceCopy (d := d) src dst x) k‖₊)) = ‖x src - x dst‖
  have hsup_le :
      Finset.univ.sup
          (fun k => ‖(x - coincidenceCopy (d := d) src dst x) k‖₊) ≤
        ‖x src - x dst‖₊ := by
    refine Finset.sup_le_iff.mpr ?_
    intro k hk
    by_cases hkdst : k = dst
    · subst k
      have hEq :
          ‖(x - coincidenceCopy (d := d) src dst x) dst‖₊ = ‖x src - x dst‖₊ := by
        apply NNReal.coe_injective
        simpa [coincidenceCopy, norm_sub_rev]
      exact le_of_eq hEq
    · simp [coincidenceCopy, hkdst]
  have hsup_ge :
      ‖x src - x dst‖₊ ≤
        Finset.univ.sup
          (fun k => ‖(x - coincidenceCopy (d := d) src dst x) k‖₊) := by
    have hmem : dst ∈ Finset.univ := by simp
    have hdst :
        ‖x src - x dst‖₊ ≤ ‖(x - coincidenceCopy (d := d) src dst x) dst‖₊ := by
      have hEq :
          ‖(x - coincidenceCopy (d := d) src dst x) dst‖₊ = ‖x src - x dst‖₊ := by
        apply NNReal.coe_injective
        simpa [coincidenceCopy, norm_sub_rev]
      exact le_of_eq hEq.symm
    exact hdst.trans (Finset.le_sup (f := fun k =>
      ‖(x - coincidenceCopy (d := d) src dst x) k‖₊) hmem)
  have hEqNN :
      Finset.univ.sup (fun k => ‖(x - coincidenceCopy (d := d) src dst x) k‖₊) =
        ‖x src - x dst‖₊ := le_antisymm hsup_le hsup_ge
  rw [show ‖x src - x dst‖ = (‖x src - x dst‖₊ : ℝ) by rfl]
  exact congrArg (fun r : NNReal => (r : ℝ)) hEqNN

omit [NeZero d] in
private theorem norm_segment_coincidenceCopy_eq_norm {n : ℕ}
    (x : NPointDomain d n) (src dst : Fin n) (hsrcdst : src ≠ dst)
    (hmax : ‖x dst‖ ≤ ‖x src‖) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖coincidenceCopy (d := d) src dst x + t •
        (x - coincidenceCopy (d := d) src dst x)‖ = ‖x‖ := by
  let y : NPointDomain d n := coincidenceCopy (d := d) src dst x
  let z : NPointDomain d n := y + t • (x - y)
  have hz_upper :
      ‖z‖ ≤ ‖x‖ := by
    change ↑(Finset.univ.sup fun k => ‖z k‖₊) ≤ ‖x‖
    have hsup :
        Finset.univ.sup (fun k => ‖z k‖₊) ≤ ‖x‖₊ := by
      refine Finset.sup_le_iff.mpr ?_
      intro k hk
      by_cases hkdst : k = dst
      · subst k
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have htnonneg : 0 ≤ 1 - t := by linarith
        have hz_dst :
            z dst = (1 - t) • x src + t • x dst := by
          ext μ
          simp [z, y, coincidenceCopy, sub_eq_add_neg]
          ring
        have hcoord :
            ‖z dst‖ ≤ ‖x‖ := by
          calc
            ‖z dst‖ = ‖(1 - t) • x src + t • x dst‖ := by rw [hz_dst]
            _ ≤ ‖(1 - t) • x src‖ + ‖t • x dst‖ := norm_add_le _ _
            _ = |1 - t| * ‖x src‖ + |t| * ‖x dst‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            _ = (1 - t) * ‖x src‖ + t * ‖x dst‖ := by
                rw [abs_of_nonneg htnonneg, abs_of_nonneg ht0]
            _ ≤ (1 - t) * ‖x‖ + t * ‖x‖ := by
                gcongr
                · exact (norm_le_pi_norm x src)
                · exact hmax.trans (norm_le_pi_norm x src)
            _ = ‖x‖ := by ring
        exact_mod_cast hcoord
      · have hz_eq : z k = x k := by
          simp [z, y, coincidenceCopy, hkdst]
        have hcoord : ‖z k‖ ≤ ‖x‖ := by
          rw [hz_eq]
          exact norm_le_pi_norm x k
        exact_mod_cast hcoord
    exact_mod_cast hsup
  have hx_le_z :
      ‖x‖ ≤ ‖z‖ := by
    change ↑(Finset.univ.sup fun k => ‖x k‖₊) ≤ ‖z‖
    have hsup :
        Finset.univ.sup (fun k => ‖x k‖₊) ≤ ‖z‖₊ := by
      refine Finset.sup_le_iff.mpr ?_
      intro k hk
      by_cases hkdst : k = dst
      · subst k
        have hzsrc : z src = x src := by
          simp [z, y, coincidenceCopy, hsrcdst]
        have hcoord : ‖x dst‖ ≤ ‖z‖ := by
          calc
            ‖x dst‖ ≤ ‖x src‖ := hmax
            _ = ‖z src‖ := by rw [hzsrc]
            _ ≤ ‖z‖ := norm_le_pi_norm z src
        exact_mod_cast hcoord
      · have hz_eq : z k = x k := by
          simp [z, y, coincidenceCopy, hkdst]
        have hcoord : ‖x k‖ ≤ ‖z‖ := by
          rw [← hz_eq]
          exact norm_le_pi_norm z k
        exact_mod_cast hcoord
    exact_mod_cast hsup
  exact le_antisymm hz_upper hx_le_z

/-- The coincidence collapse gives a concrete diagonal point within pair-distance
    `‖x i - x j‖` of `x`. -/
theorem infDist_CoincidenceLocus_le_pairDifference {d n : ℕ}
    (x : NPointDomain d n) (i j : Fin n) (hij : i ≠ j) :
    Metric.infDist x (CoincidenceLocus d n) ≤ ‖x i - x j‖ := by
  refine (Metric.infDist_le_dist_of_mem
    (coincidenceCollapse_mem_CoincidenceLocus (d := d) x i j hij)).trans ?_
  simpa [dist_eq_norm] using
    norm_sub_coincidenceCollapse_le_pairDifference (d := d) x i j hij

/-- The coincidence locus is closed: it is a finite union of pairwise-equality
    hyperplanes `{x | x i = x j}`. -/
theorem isClosed_CoincidenceLocus {d n : ℕ} :
    IsClosed (CoincidenceLocus d n) := by
  classical
  have hEq :
      CoincidenceLocus d n =
        ⋃ i : Fin n, ⋃ j : Fin n,
          if h : i = j then (∅ : Set (NPointDomain d n)) else {x | x i = x j} := by
    ext x
    simp [CoincidenceLocus]
  rw [hEq]
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro j
  by_cases h : i = j
  · simp [h]
  · simpa [h] using (isClosed_eq (continuous_apply i) (continuous_apply j))

/-- If the coincidence locus is nonempty, some pair separation is controlled by
    twice the distance to that locus. This is the converse metric comparison to
    `infDist_CoincidenceLocus_le_pairDifference`. -/
theorem exists_pairDifference_le_two_infDist_CoincidenceLocus {d n : ℕ}
    (x : NPointDomain d n) (hcoin : (CoincidenceLocus d n).Nonempty) :
    ∃ i j : Fin n, i ≠ j ∧
      ‖x i - x j‖ ≤ 2 * Metric.infDist x (CoincidenceLocus d n) := by
  have hclosed : IsClosed (CoincidenceLocus d n) := isClosed_CoincidenceLocus (d := d) (n := n)
  obtain ⟨y, hyCoin, hyDist⟩ := hclosed.exists_infDist_eq_dist hcoin x
  rcases hyCoin with ⟨i, j, hij, hEq⟩
  refine ⟨i, j, hij, ?_⟩
  have hi : ‖x i - y i‖ ≤ ‖x - y‖ := by
    simpa [Pi.sub_apply] using (norm_le_pi_norm (x - y) i)
  have hj : ‖x j - y j‖ ≤ ‖x - y‖ := by
    simpa [Pi.sub_apply] using (norm_le_pi_norm (x - y) j)
  calc
    ‖x i - x j‖ = ‖(x i - y i) - (x j - y i)‖ := by
      rw [sub_sub_sub_cancel_right]
    _ = ‖(x i - y i) - (x j - y j)‖ := by simpa [hEq]
    _ ≤ ‖x i - y i‖ + ‖x j - y j‖ := norm_sub_le _ _
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add hi hj
    _ = 2 * ‖x - y‖ := by ring
    _ = 2 * Metric.infDist x (CoincidenceLocus d n) := by
      rw [hyDist, dist_eq_norm]

set_option maxHeartbeats 800000 in
/-- Global weighted flatness in a fixed pairwise separation: infinite-order vanishing
    on the coincidence locus combined with Schwartz decay at spatial infinity. -/
theorem VanishesToInfiniteOrderOnCoincidence.one_add_norm_pow_mul_norm_le_pairDifference_pow_succ
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (N m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C * ‖x i - x j‖ ^ (m + 1) := by
  let sem := (Finset.Iic (N, m + 1)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
  let A : ℝ := 2 ^ N * sem f
  refine ⟨A / (((Nat.factorial m : ℕ) : ℝ)), by positivity, ?_⟩
  intro x
  let src : Fin n := if h : ‖x i‖ ≤ ‖x j‖ then j else i
  let dst : Fin n := if h : ‖x i‖ ≤ ‖x j‖ then i else j
  have hsrcdst : src ≠ dst := by
    dsimp [src, dst]
    split_ifs
    · simpa using hij.symm
    · simpa using hij
  have hmax : ‖x dst‖ ≤ ‖x src‖ := by
    dsimp [src, dst]
    split_ifs with h
    · simpa using h
    · exact le_of_not_ge h
  have hpair :
      ‖x src - x dst‖ = ‖x i - x j‖ := by
    dsimp [src, dst]
    split_ifs <;> simp [norm_sub_rev]
  let c : NPointDomain d n := coincidenceCopy (d := d) src dst x
  let v : NPointDomain d n := x - c
  let L : ℝ →L[ℝ] NPointDomain d n :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) :=
    fun r => by
      simpa using ((f : SchwartzNPoint d n).smooth r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_coin : c ∈ CoincidenceLocus d n := by
    simpa [c] using coincidenceCopy_mem_CoincidenceLocus (d := d) x src dst hsrcdst
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_mem : k ∈ Finset.range (m + 1) := hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ) (L 0 + c) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hf k c hc_coin
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hsem_bound :
        (1 + ‖L t + c‖) ^ N *
            ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤ A := by
      simpa [A, sem] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (N, m + 1)) (k := N) (n := m + 1)
          le_rfl le_rfl f (L t + c))
    have hnorm_seg : ‖L t + c‖ = ‖x‖ := by
      simpa [L, v, c, ContinuousLinearMap.smulRight_apply, add_comm, add_left_comm, add_assoc]
        using norm_segment_coincidenceCopy_eq_norm (d := d) x src dst hsrcdst hmax t ht
    have hpow_pos : 0 < (1 + ‖x‖) ^ N := by positivity
    have hA :
        ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤
          A / (1 + ‖x‖) ^ N := by
      rw [le_div_iff₀ hpow_pos]
      simpa [hnorm_seg, mul_comm, mul_left_comm, mul_assoc] using hsem_bound
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simpa [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul, mul_comm] using
        (norm_smul s v)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ)
            (z + c)) (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (A / (1 + ‖x‖) ^ N) * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
      _ = (A / (1 + ‖x‖) ^ N) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1) := by
          gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hv :
      ‖v‖ = ‖x i - x j‖ := by
    simpa [v, c, hpair] using
      norm_sub_coincidenceCopy_eq_pairDifference (d := d) x src dst
  have hg_one : g 1 = f x := by
    simp [g, L, v, c, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg, add_comm, add_left_comm,
      ]
  have hpow_nonneg : 0 ≤ (1 + ‖x‖) ^ N := by positivity
  calc
    (1 + ‖x‖) ^ N * ‖f x‖ =
        (1 + ‖x‖) ^ N * ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
          rw [hg_one]
          simp [hTaylor_zero]
    _ ≤ (1 + ‖x‖) ^ N *
          (((A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1)) *
            (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (by simpa [hTaylor_zero] using hrem) hpow_nonneg
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) := by
          have hpow_ne : (1 + ‖x‖) ^ N ≠ 0 := by positivity
          field_simp [hpow_ne, Nat.cast_ne_zero]
          ring
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x i - x j‖ ^ (m + 1) := by
          rw [hv]

/-- Global weighted flatness in terms of actual distance to the coincidence locus. -/
theorem VanishesToInfiniteOrderOnCoincidence.one_add_norm_pow_mul_norm_le_infDist_CoincidenceLocus_pow_succ
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (N m : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
  classical
  let P : Type := {p : Fin n × Fin n // p.1 ≠ p.2}
  have hP_nonempty : Nonempty P := by
    rcases hcoin with ⟨x, hx⟩
    rcases hx with ⟨i, j, hij, _⟩
    exact ⟨⟨(i, j), hij⟩⟩
  have hpair :
      ∀ p : P, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C * ‖x p.1.1 - x p.1.2‖ ^ (m + 1) := by
    intro p
    exact
      VanishesToInfiniteOrderOnCoincidence.one_add_norm_pow_mul_norm_le_pairDifference_pow_succ
        hf N m p.1.1 p.1.2 p.2
  choose C hC_nonneg hC_bound using hpair
  let Cmax : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hC_le : ∀ p : P, C p ≤ Cmax := by
    intro p
    exact Finset.le_sup' (f := C) (Finset.mem_univ p)
  let p0 : P := Classical.choice hP_nonempty
  have hCmax_nonneg : 0 ≤ Cmax := le_trans (hC_nonneg p0) (hC_le p0)
  refine ⟨Cmax * (2 : ℝ) ^ (m + 1), mul_nonneg hCmax_nonneg (pow_nonneg (by norm_num) _), ?_⟩
  intro x
  obtain ⟨i, j, hij, hijdist⟩ :=
    exists_pairDifference_le_two_infDist_CoincidenceLocus (d := d) (n := n) x hcoin
  let p : P := ⟨(i, j), hij⟩
  calc
    (1 + ‖x‖) ^ N * ‖f x‖ ≤ C p * ‖x i - x j‖ ^ (m + 1) := hC_bound p x
    _ ≤ Cmax * ‖x i - x j‖ ^ (m + 1) := by
        exact mul_le_mul_of_nonneg_right (hC_le p) (pow_nonneg (norm_nonneg _) _)
    _ ≤ Cmax * (2 * Metric.infDist x (CoincidenceLocus d n)) ^ (m + 1) := by
        gcongr
    _ = (Cmax * (2 : ℝ) ^ (m + 1)) * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
        rw [mul_pow]
        ring

set_option maxHeartbeats 400000 in
/-- Explicit-constant version of the pairDifference vanishing bound.

    The constant `2^N * sem / m!` (where `sem` is the `(N, m+1)` Schwartz seminorm)
    is made explicit rather than hidden behind `∃`. This is needed in the
    continuity proof for `constructSchwingerFunctions` where we must exhibit a
    seminorm-linear bound `‖T f‖ ≤ C * sem(f)` with `C` independent of `f`. -/
theorem VanishesToInfiniteOrderOnCoincidence.weighted_pairDifference_bound_explicit
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (N m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∀ x : NPointDomain d n,
      (1 + ‖x‖) ^ N * ‖f x‖ ≤
        (2 ^ N * ((Finset.Iic (N, m + 1)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f /
          (Nat.factorial m : ℝ)) * ‖x i - x j‖ ^ (m + 1) := by
  -- This extracts the explicit constant from the proof of
  -- one_add_norm_pow_mul_norm_le_pairDifference_pow_succ.
  -- We reproduce the same argument since the constant A/m! is exactly what we claim.
  let sem := (Finset.Iic (N, m + 1)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
  let A : ℝ := 2 ^ N * sem f
  -- The bound follows from the same argument as
  -- one_add_norm_pow_mul_norm_le_pairDifference_pow_succ.
  -- We set up the same proof structure.
  intro x
  let src : Fin n := if h : ‖x i‖ ≤ ‖x j‖ then j else i
  let dst : Fin n := if h : ‖x i‖ ≤ ‖x j‖ then i else j
  have hsrcdst : src ≠ dst := by
    dsimp [src, dst]
    split_ifs
    · simpa using hij.symm
    · simpa using hij
  have hmax : ‖x dst‖ ≤ ‖x src‖ := by
    dsimp [src, dst]
    split_ifs with h
    · simpa using h
    · exact le_of_not_ge h
  have hpair :
      ‖x src - x dst‖ = ‖x i - x j‖ := by
    dsimp [src, dst]
    split_ifs <;> simp [norm_sub_rev]
  let c : NPointDomain d n := coincidenceCopy (d := d) src dst x
  let v : NPointDomain d n := x - c
  let L : ℝ →L[ℝ] NPointDomain d n :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c)) :=
    fun r => by
      simpa using ((f : SchwartzNPoint d n).smooth r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_coin : c ∈ CoincidenceLocus d n := by
    simpa [c] using coincidenceCopy_mem_CoincidenceLocus (d := d) x src dst hsrcdst
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_mem : k ∈ Finset.range (m + 1) := hk
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ) (L 0 + c) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hf k c hc_coin
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1) := by
    intro t ht
    have hsem_bound :
        (1 + ‖L t + c‖) ^ N *
            ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤ A := by
      simpa [A, sem] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (N, m + 1)) (k := N) (n := m + 1)
          le_rfl le_rfl f (L t + c))
    have hnorm_seg : ‖L t + c‖ = ‖x‖ := by
      simpa [L, v, c, ContinuousLinearMap.smulRight_apply, add_comm, add_left_comm, add_assoc]
        using norm_segment_coincidenceCopy_eq_norm (d := d) x src dst hsrcdst hmax t ht
    have hpow_pos : 0 < (1 + ‖x‖) ^ N := by positivity
    have hA :
        ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ ≤
          A / (1 + ‖x‖) ^ N := by
      rw [le_div_iff₀ hpow_pos]
      simpa [hnorm_seg, mul_comm, mul_left_comm, mul_assoc] using hsem_bound
    have hL :
        ‖L‖ ≤ ‖v‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
      simpa [L, ContinuousLinearMap.smulRight_apply, Real.norm_eq_abs, norm_smul, mul_comm] using
        (norm_smul s v)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
      ((hg_contDiff (m + 1)).contDiffAt) ht, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcomp :
        iteratedFDeriv ℝ (m + 1) g t =
          (iteratedFDeriv ℝ (m + 1) (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ)
            (z + c)) (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ (A / (1 + ‖x‖) ^ N) * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
      _ = (A / (1 + ‖x‖) ^ N) * ‖L‖ ^ (m + 1) := by simp
      _ ≤ (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1) := by
          gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := (A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hv :
      ‖v‖ = ‖x i - x j‖ := by
    simpa [v, c, hpair] using
      norm_sub_coincidenceCopy_eq_pairDifference (d := d) x src dst
  have hg_one : g 1 = f x := by
    simp [g, L, v, c, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg, add_comm, add_left_comm,
      ]
  have hpow_nonneg : 0 ≤ (1 + ‖x‖) ^ N := by positivity
  calc
    (1 + ‖x‖) ^ N * ‖f x‖ =
        (1 + ‖x‖) ^ N * ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
          rw [hg_one]
          simp [hTaylor_zero]
    _ ≤ (1 + ‖x‖) ^ N *
          (((A / (1 + ‖x‖) ^ N) * ‖v‖ ^ (m + 1)) *
            (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left (by simpa [hTaylor_zero] using hrem) hpow_nonneg
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) := by
          have hpow_ne : (1 + ‖x‖) ^ N ≠ 0 := by positivity
          field_simp [hpow_ne, Nat.cast_ne_zero]
          ring
    _ = (A / (((Nat.factorial m : ℕ) : ℝ))) * ‖x i - x j‖ ^ (m + 1) := by
          rw [hv]

/-- Explicit-constant version of the infDist vanishing bound: the constant factor
    (independent of `f`) is `2^(N+m+1) / m!`, multiplied by the `(N, m+1)` Schwartz
    seminorm of `f`.

    This refines `one_add_norm_pow_mul_norm_le_infDist_CoincidenceLocus_pow_succ` by
    making the constant explicit. Needed for the `constructSchwingerFunctions` continuity
    proof where we must exhibit a seminorm-linear bound `‖T f‖ ≤ C * sem(f)`. -/
theorem VanishesToInfiniteOrderOnCoincidence.weighted_infDist_bound_explicit
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (N m : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty) :
    ∀ x : NPointDomain d n,
      (1 + ‖x‖) ^ N * ‖f x‖ ≤
        (2 ^ (N + m + 1) / (Nat.factorial m : ℝ)) *
          ((Finset.Iic (N, m + 1)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)) f *
          Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
  let sem := (Finset.Iic (N, m + 1)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
  let A : ℝ := 2 ^ N * sem f
  let C_pair : ℝ := A / (Nat.factorial m : ℝ)
  intro x
  obtain ⟨i, j, hij, hijdist⟩ :=
    exists_pairDifference_le_two_infDist_CoincidenceLocus (d := d) (n := n) x hcoin
  have hpair_bound :=
    VanishesToInfiniteOrderOnCoincidence.weighted_pairDifference_bound_explicit
      hf N m i j hij x
  calc (1 + ‖x‖) ^ N * ‖f x‖
      ≤ C_pair * ‖x i - x j‖ ^ (m + 1) := hpair_bound
    _ ≤ C_pair * (2 * Metric.infDist x (CoincidenceLocus d n)) ^ (m + 1) := by
        gcongr
    _ = C_pair * (2 ^ (m + 1) * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1)) := by
        rw [mul_pow]
    _ = (C_pair * 2 ^ (m + 1)) * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by ring
    _ = (2 ^ (N + m + 1) / (Nat.factorial m : ℝ)) * sem f *
          Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
        simp only [C_pair, A]
        rw [pow_add, pow_add]
        field_simp
        ring

/-- The `ℂ`-submodule of Schwartz n-point functions vanishing to infinite order
    on the coincidence locus. -/
def zeroDiagonalSubmodule (d n : ℕ) : Submodule ℂ (SchwartzNPoint d n) where
  carrier := { f | VanishesToInfiniteOrderOnCoincidence f }
  zero_mem' := by
    intro k x hx
    by_cases hk : k = 0
    · subst hk
      ext m
      simp
    · change iteratedFDeriv ℝ k (fun _ : NPointDomain d n => (0 : ℂ)) x = 0
      exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) hk (0 : ℂ)) x
  add_mem' := by
    intro f g hf hg k x hx
    simpa using
      (iteratedFDeriv_add_apply
        ((f : SchwartzNPoint d n).smooth _).contDiffAt
        ((g : SchwartzNPoint d n).smooth _).contDiffAt).trans
        (by rw [hf k x hx, hg k x hx, zero_add])
  smul_mem' := by
    intro c f hf k x hx
    simpa using
      (iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c)
        (((f : SchwartzNPoint d n).smooth _).contDiffAt)).trans
        (by rw [hf k x hx, smul_zero])

/-- The OS-I zero-diagonal Schwartz test space. -/
def ZeroDiagonalSchwartz (d n : ℕ) :=
  ↥(zeroDiagonalSubmodule d n)

instance instAddCommMonoidZeroDiagonalSchwartz (d n : ℕ) :
    AddCommMonoid (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instModuleZeroDiagonalSchwartz (d n : ℕ) :
    Module ℂ (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instTopologicalSpaceZeroDiagonalSchwartz (d n : ℕ) :
    TopologicalSpace (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instContinuousAddZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousAdd (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instContinuousConstSMulZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousConstSMul ℂ (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

/-- A classical promotion from a Schwartz test function to the zero-diagonal
    subspace, with a junk zero fallback when the function is not in `°S`.

    This keeps definitions such as `OSInnerProduct` total while ensuring that,
    whenever a genuine zero-diagonal witness exists, the promoted term reduces
    to the intended branch. -/
noncomputable def ZeroDiagonalSchwartz.ofClassical {d n : ℕ}
    (f : SchwartzNPoint d n) : ZeroDiagonalSchwartz d n := by
  classical
  by_cases h : VanishesToInfiniteOrderOnCoincidence f
  · exact ⟨f, h⟩
  · exact 0

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_of_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : VanishesToInfiniteOrderOnCoincidence f) :
    ZeroDiagonalSchwartz.ofClassical f = ⟨f, h⟩ := by
  classical
  simp [ZeroDiagonalSchwartz.ofClassical, h]

@[simp]
theorem ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : VanishesToInfiniteOrderOnCoincidence f) :
    (ZeroDiagonalSchwartz.ofClassical f).1 = f := by
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f) h]

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_of_not_vanishes {d n : ℕ}
    (f : SchwartzNPoint d n) (h : ¬ VanishesToInfiniteOrderOnCoincidence f) :
    ZeroDiagonalSchwartz.ofClassical f = 0 := by
  classical
  simp [ZeroDiagonalSchwartz.ofClassical, h]

@[simp]
theorem VanishesToInfiniteOrderOnCoincidence.zero {d n : ℕ} :
    VanishesToInfiniteOrderOnCoincidence (0 : SchwartzNPoint d n) := by
  intro k x hx
  exact congrFun
    (iteratedFDeriv_zero_fun (𝕜 := ℝ) (n := k)
      (E := NPointDomain d n) (F := ℂ)) x

theorem VanishesToInfiniteOrderOnCoincidence.add {d n : ℕ}
    {f g : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hg : VanishesToInfiniteOrderOnCoincidence g) :
    VanishesToInfiniteOrderOnCoincidence (f + g) := by
  change f + g ∈ zeroDiagonalSubmodule d n
  exact (zeroDiagonalSubmodule d n).add_mem hf hg

theorem VanishesToInfiniteOrderOnCoincidence.smul {d n : ℕ}
    (c : ℂ) {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (c • f) := by
  change c • f ∈ zeroDiagonalSubmodule d n
  exact (zeroDiagonalSubmodule d n).smul_mem c hf

private theorem mem_CoincidenceLocus_precomp_equiv {d k l : ℕ}
    (σ : Fin k ≃ Fin l) {x : NPointDomain d l}
    (hx : x ∈ CoincidenceLocus d l) :
    (fun i => x (σ i)) ∈ CoincidenceLocus d k := by
  rcases hx with ⟨i, j, hij, hEq⟩
  refine ⟨σ.symm i, σ.symm j, ?_, ?_⟩
  · intro h
    apply hij
    simpa using congrArg σ h
  · simpa using hEq

/-- Vanishing to infinite order on the coincidence locus is preserved by
    reindexing the point variables by any finite equivalence. -/
theorem VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
    {d k l : ℕ} {f : SchwartzNPoint d k}
    (hf : VanishesToInfiniteOrderOnCoincidence f) (σ : Fin k ≃ Fin l) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv) f) := by
  intro r x hx
  let e : NPointDomain d l ≃L[ℝ] NPointDomain d k :=
    (LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv
  have hcomp :
      iteratedFDeriv ℝ r
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f : SchwartzNPoint d l) :
            NPointDomain d l → ℂ) x =
        (iteratedFDeriv ℝ r (f : NPointDomain d k → ℂ) (e x)).compContinuousLinearMap
          (fun _ : Fin r => e.toContinuousLinearMap) := by
    simpa [e] using
      e.toContinuousLinearMap.iteratedFDeriv_comp_right
        (f := (f : NPointDomain d k → ℂ))
        ((f : SchwartzNPoint d k).smooth r) (x := x) (i := r) le_rfl
  have hzero :
      iteratedFDeriv ℝ r (f : NPointDomain d k → ℂ) (e x) = 0 := by
    exact hf r (e x) (by
      simpa [e] using mem_CoincidenceLocus_precomp_equiv (d := d) (σ := σ) hx)
  rw [hcomp, hzero]
  ext u
  simp

omit [NeZero d] in
abbrev reindexSchwartz {k l : ℕ} (σ : Fin k ≃ Fin l) (f : SchwartzNPoint d k) :
    SchwartzNPoint d l :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv) f

omit [NeZero d] in
@[simp] theorem reindexSchwartz_apply {k l : ℕ} (σ : Fin k ≃ Fin l)
    (f : SchwartzNPoint d k) (x : NPointDomain d l) :
    reindexSchwartz (d := d) σ f x = f (fun i => x (σ i)) := by
  rfl

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_zero {d n : ℕ} :
    ZeroDiagonalSchwartz.ofClassical (0 : SchwartzNPoint d n) = 0 := by
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := (0 : SchwartzNPoint d n))
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n))]
  rfl

theorem ZeroDiagonalSchwartz.ofClassical_add_of_vanishes {d n : ℕ}
    (f g : SchwartzNPoint d n)
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hg : VanishesToInfiniteOrderOnCoincidence g) :
    ZeroDiagonalSchwartz.ofClassical (f + g) =
      ZeroDiagonalSchwartz.ofClassical f + ZeroDiagonalSchwartz.ofClassical g := by
  have hfg : VanishesToInfiniteOrderOnCoincidence (f + g) := hf.add hg
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f + g) hfg,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f) hf,
    ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := g) hg]
  rfl

@[simp]
theorem ZeroDiagonalSchwartz.ofClassical_smul {d n : ℕ}
    (c : ℂ) (f : SchwartzNPoint d n) :
    ZeroDiagonalSchwartz.ofClassical (c • f) =
      c • ZeroDiagonalSchwartz.ofClassical f := by
  classical
  by_cases hc : c = 0
  · subst hc
    rw [show (0 : ℂ) • f = (0 : SchwartzNPoint d n) by simp,
      ZeroDiagonalSchwartz.ofClassical_zero]
    simp
  · by_cases hf : VanishesToInfiniteOrderOnCoincidence f
    · have hcf : VanishesToInfiniteOrderOnCoincidence (c • f) := hf.smul c
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := c • f) hcf,
        ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := f) hf]
      rfl
    · have hcf : ¬ VanishesToInfiniteOrderOnCoincidence (c • f) := by
        intro hcf
        apply hf
        simpa [smul_smul, hc] using hcf.smul c⁻¹
      rw [ZeroDiagonalSchwartz.ofClassical_of_not_vanishes (f := c • f) hcf,
        ZeroDiagonalSchwartz.ofClassical_of_not_vanishes (f := f) hf]
      simp

/-- If varying one factor of a product tensor always stays in the OS zero-diagonal
subspace, then that slot defines a continuous linear map into
`ZeroDiagonalSchwartz`. -/
def ZeroDiagonalSchwartz.productTensorUpdateCLM {d n : ℕ} [NeZero d]
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d)
    (hvanish : ∀ f : SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence
        (SchwartzMap.productTensor (Function.update fs i f))) :
    SchwartzSpacetime d →L[ℂ] ZeroDiagonalSchwartz d n where
  toLinearMap :=
    { toFun := fun f =>
        ⟨SchwartzMap.productTensor (Function.update fs i f), hvanish f⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        change
          SchwartzMap.productTensor (Function.update fs i (f + g)) =
            SchwartzMap.productTensor (Function.update fs i f) +
              SchwartzMap.productTensor (Function.update fs i g)
        simp [SchwartzMap.productTensor_update_add]
      map_smul' := by
        intro c f
        apply Subtype.ext
        change
          SchwartzMap.productTensor (Function.update fs i (c • f)) =
            c • SchwartzMap.productTensor (Function.update fs i f)
        simp [SchwartzMap.productTensor_update_smul] }
  cont := by
    let hbase : Continuous (fun f : SchwartzSpacetime d =>
      SchwartzMap.productTensor (Function.update fs i f)) :=
      SchwartzMap.productTensor_continuous_arg i fs
    exact hbase.subtype_mk (fun f => hvanish f)

@[simp]
theorem ZeroDiagonalSchwartz.productTensorUpdateCLM_apply {d n : ℕ} [NeZero d]
    (i : Fin n) (fs : Fin n → SchwartzSpacetime d)
    (hvanish : ∀ f : SchwartzSpacetime d,
      VanishesToInfiniteOrderOnCoincidence
        (SchwartzMap.productTensor (Function.update fs i f)))
    (f : SchwartzSpacetime d) :
    ZeroDiagonalSchwartz.productTensorUpdateCLM (d := d) i fs hvanish f =
      ⟨SchwartzMap.productTensor (Function.update fs i f), hvanish f⟩ := rfl

/-- Zero-diagonal Schwinger families, i.e. Euclidean correlation functionals
    defined only on the OS-I test space `°S`. This is the honest Wightman -> OS-I
    codomain before any separate extension to the full Schwartz space. -/
def ZeroDiagonalSchwingerFunctions (d : ℕ) := (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ

/-- Honest Schwinger functions (Euclidean correlators) on the corrected OS-I
    test space `°S = ZeroDiagonalSchwartz`.

    This is the notion that should be used for Schwinger data in the project. -/
abbrev SchwingerFunctions (d : ℕ) := ZeroDiagonalSchwingerFunctions d

/-- If a Schwartz test function is supported in the strict ordered positive-time
    region, then it vanishes to infinite order on the coincidence locus.

    This is the precise bridge from the OS-I positivity sector `S^<_{+}` to the
    zero-diagonal space `°S`: coincidence points lie outside the ordered-time
    region, and every iterated derivative is supported inside the support of the
    original Schwartz function. -/
theorem VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
    {d n : ℕ} (f : SchwartzNPoint d n)
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    VanishesToInfiniteOrderOnCoincidence f := by
  intro k x hxcoin
  have hx_not_ord : x ∉ OrderedPositiveTimeRegion d n := by
    intro hxord
    exact (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion hxord) hxcoin
  have hx_not_support :
      x ∉ Function.support (iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ)) := by
    intro hx
    have hx' := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) (f := ⇑f) hx
    exact hx_not_ord (hsupp hx')
  by_contra hx_nonzero
  exact hx_not_support (by simpa [Function.mem_support, hx_nonzero])

/-- Time reflection operator on Euclidean points: θ(τ, x⃗) = (-τ, x⃗) -/
def timeReflection (x : SpacetimeDim d) : SpacetimeDim d :=
  fun i => if i = 0 then -x 0 else x i

/-- Time reflection on n-point configurations -/
def timeReflectionN (x : NPointDomain d n) : NPointDomain d n :=
  fun i => timeReflection d (x i)

/-- Time reflection preserves Lebesgue measure on spacetime. -/
theorem timeReflection_measurePreserving :
    MeasureTheory.MeasurePreserving (timeReflection d) MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show timeReflection (d := d) =
      (fun (x : SpacetimeDim d) (i : Fin (d + 1)) =>
        (if i = 0 then Neg.neg else id) (x i)) by
      funext x i
      by_cases hi : i = 0
      · subst hi
        simp [timeReflection]
      · simp [timeReflection, hi]]
  exact MeasureTheory.volume_preserving_pi (fun i : Fin (d + 1) => by
    by_cases hi : i = 0
    · simpa [hi] using
        (MeasureTheory.Measure.measurePreserving_neg
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    · simpa [hi] using
        (MeasureTheory.MeasurePreserving.id (MeasureTheory.volume : MeasureTheory.Measure ℝ)))

/-- Time reflection preserves Lebesgue measure on n-point configuration space. -/
theorem timeReflectionN_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (timeReflectionN (d := d) (n := n)) MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show timeReflectionN (d := d) (n := n) =
      (fun (x : NPointDomain d n) (i : Fin n) => timeReflection (d := d) (x i)) by
      funext x i
      rfl]
  exact MeasureTheory.volume_preserving_pi
    (fun _ : Fin n => timeReflection_measurePreserving (d := d))

/-- Reversing the order of points preserves Lebesgue measure on n-point configuration space. -/
theorem reverseNPoint_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => x (Fin.rev i))
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  let e : Fin n ≃ Fin n :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => SpacetimeDim d) e : _ → _)
      = (fun x : NPointDomain d n => fun i : Fin n => x (Fin.rev i)) := by
    funext x
    let x' : (a : Fin n) → (fun _ : Fin n => SpacetimeDim d) (e a) := x
    funext i
    simpa [e] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => SpacetimeDim d) (e := e) x'
        (Fin.rev i))
  exact heq ▸
    (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin n => SpacetimeDim d) e)

/-- The real OS reflection map (reverse the point order and reflect Euclidean time) preserves
    Lebesgue measure on configuration space. -/
theorem osReflectionN_measurePreserving {n : ℕ} :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => timeReflection d (x (Fin.rev i)))
      MeasureTheory.volume MeasureTheory.volume := by
  let revMap : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  let thetaMap : NPointDomain d n → NPointDomain d n := timeReflectionN (d := d) (n := n)
  have hcomp :
      (fun x : NPointDomain d n => fun i : Fin n => timeReflection d (x (Fin.rev i))) =
        thetaMap ∘ revMap := by
    rfl
  rw [hcomp]
  exact (timeReflectionN_measurePreserving (d := d) (n := n)).comp
    (reverseNPoint_measurePreserving (d := d) (n := n))

/-- Time reflection is an involution: θ(θx) = x. -/
theorem timeReflection_timeReflection (x : SpacetimeDim d) :
    timeReflection d (timeReflection d x) = x := by
  funext j; simp only [timeReflection]; by_cases hj : j = 0 <;> simp [hj]

/-- Time reflection preserves the NNNorm of spacetime vectors. -/
private theorem timeReflection_nnnorm_eq (y : SpacetimeDim d) :
    ‖timeReflection d y‖₊ = ‖y‖₊ := by
  simp only [Pi.nnnorm_def, timeReflection]
  apply Finset.sup_congr rfl; intro j _
  by_cases hj : j = 0
  · subst hj; simp [nnnorm_neg]
  · simp [if_neg hj]

/-- Time reflection preserves the norm of n-point configurations. -/
private theorem timeReflectionN_norm_eq (x : NPointDomain d n) :
    ‖timeReflectionN d x‖ = ‖x‖ := by
  simp only [Pi.norm_def, timeReflectionN]
  congr 1
  apply Finset.sup_congr rfl; intro i _
  exact_mod_cast timeReflection_nnnorm_eq d (x i)

/-- Time reflection on n-point domains is smooth (it is linear). -/
private theorem contDiff_timeReflectionN {m : WithTop ℕ∞} :
    ContDiff ℝ m (timeReflectionN (n := n) d) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  show ContDiff ℝ m fun x => timeReflectionN d x i j
  simp only [timeReflectionN, timeReflection]
  by_cases hj : j = 0
  · subst hj; simp only [ite_true]
    exact (contDiff_apply_apply ℝ ℝ i (0 : Fin (d + 1))).neg
  · simp only [if_neg hj]
    exact contDiff_apply_apply ℝ ℝ i j

section TimeReflectSchwartz
variable {d}

/-- Time reflection on n-point Schwartz functions.
    (θf)(x₁,...,xₙ) = f(θx₁,...,θxₙ) where θ(τ,x⃗) = (-τ,x⃗).

    This is the correct involution for the Osterwalder-Schrader inner product.
    The OS reflection positivity uses ⟨F, G⟩_OS = Σ S_{n+m}((θf̄)_n ⊗ g_m),
    NOT the Borchers involution (which includes argument reversal).

    Reference: Osterwalder-Schrader, Commun. Math. Phys. 31 (1973), Axiom E2 -/
def SchwartzNPoint.timeReflect {n : ℕ} (f : SchwartzNPoint d n) : SchwartzNPoint d n where
  toFun := fun x => f (timeReflectionN d x)
  smooth' := by exact f.smooth'.comp (contDiff_timeReflectionN d)
  decay' := by
    intro k l
    obtain ⟨C, hC⟩ := f.decay' k l
    refine ⟨C, fun x => ?_⟩
    let θLE : NPointDomain d n ≃ₗ[ℝ] NPointDomain d n :=
      { toFun := timeReflectionN d
        invFun := timeReflectionN d
        left_inv := fun x => funext fun i => timeReflection_timeReflection d (x i)
        right_inv := fun x => funext fun i => timeReflection_timeReflection d (x i)
        map_add' := fun x y => by
          funext i j; simp only [timeReflectionN, timeReflection, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c x => by
          funext i j
          simp only [timeReflectionN, timeReflection, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          split_ifs <;> ring }
    let θLIE : NPointDomain d n ≃ₗᵢ[ℝ] NPointDomain d n :=
      { θLE with
        norm_map' := fun x => timeReflectionN_norm_eq d x }
    have hcomp : (fun x => f (timeReflectionN d x)) = f ∘ θLIE := rfl
    rw [hcomp, θLIE.norm_iteratedFDeriv_comp_right (𝕜 := ℝ) f x l,
      show ‖x‖ = ‖θLIE x‖ from (θLIE.norm_map x).symm]
    exact hC _

@[simp]
theorem SchwartzNPoint.timeReflect_apply {n : ℕ} (f : SchwartzNPoint d n)
    (x : NPointDomain d n) :
    f.timeReflect x = f (timeReflectionN d x) := rfl

/-- Time reflection does not increase Schwartz seminorms. -/
theorem SchwartzNPoint.seminorm_timeReflect_le {n : ℕ} (k l : ℕ)
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ k l f.timeReflect ≤ SchwartzMap.seminorm ℝ k l f := by
  refine SchwartzMap.seminorm_le_bound ℝ k l f.timeReflect
    (by positivity) ?_
  intro x
  let θLE : NPointDomain d n ≃ₗ[ℝ] NPointDomain d n :=
    { toFun := timeReflectionN d
      invFun := timeReflectionN d
      left_inv := fun y => funext fun i => timeReflection_timeReflection d (y i)
      right_inv := fun y => funext fun i => timeReflection_timeReflection d (y i)
      map_add' := fun y z => by
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c y => by
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        split_ifs <;> ring }
  let θLIE : NPointDomain d n ≃ₗᵢ[ℝ] NPointDomain d n :=
    { θLE with
      norm_map' := fun y => timeReflectionN_norm_eq d y }
  have hcomp : (fun y => f (timeReflectionN d y)) = f ∘ θLIE := rfl
  rw [show ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f.timeReflect) x‖ =
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => f (timeReflectionN d y)) x‖ by rfl]
  rw [hcomp, θLIE.norm_iteratedFDeriv_comp_right (𝕜 := ℝ) f x l,
    show ‖x‖ = ‖θLIE x‖ from (θLIE.norm_map x).symm]
  exact SchwartzMap.le_seminorm ℝ k l f (θLIE x)

/-- The Osterwalder-Schrader conjugation: time reflection + complex conjugation.
    (θf̄)(x₁,...,xₙ) = conj(f(θx₁,...,θxₙ))

    This is the correct involution for the OS inner product. Compare with
    `borchersConj` (argument reversal + conjugation) for Wightman functions.

    Reference: Osterwalder-Schrader, Commun. Math. Phys. 31 (1973), §2 -/
def SchwartzNPoint.osConj {n : ℕ} (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  f.timeReflect.conj

@[simp]
theorem SchwartzNPoint.osConj_apply {n : ℕ} (f : SchwartzNPoint d n)
    (x : NPointDomain d n) :
    f.osConj x = starRingEnd ℂ (f (timeReflectionN d x)) := rfl

/-- The OS conjugation does not increase Schwartz seminorms. -/
theorem SchwartzNPoint.seminorm_osConj_le {n : ℕ} (k l : ℕ)
    (f : SchwartzNPoint d n) :
    SchwartzMap.seminorm ℝ k l f.osConj ≤ SchwartzMap.seminorm ℝ k l f := by
  exact (SchwartzMap.seminorm_conj_le k l f.timeReflect).trans
    (SchwartzNPoint.seminorm_timeReflect_le (d := d) k l f)

/-- The OS conjugated tensor product: (θf̄) ⊗ g.
    This is the pairing used in the OS inner product for Schwinger functions:
    ⟨F, G⟩_OS = Σ S_{n+m}((θf̄)_n ⊗ g_m)

    Compare with `conjTensorProduct` (Borchers involution) used in
    `WightmanInnerProduct`. -/
def SchwartzNPoint.osConjTensorProduct {m k : ℕ} (f : SchwartzNPoint d m)
    (g : SchwartzNPoint d k) : SchwartzNPoint d (m + k) :=
  f.osConj.tensorProduct g

omit [NeZero d] in
private theorem tsupport_precomp_subset {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem continuous_timeReflectionN {n : ℕ} :
    Continuous (timeReflectionN d (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simpa [timeReflectionN, timeReflection] using
      ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
        Continuous fun x : NPointDomain d n => -x i 0)
  · simpa [timeReflectionN, timeReflection, hμ] using
      ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
        (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
        Continuous fun x : NPointDomain d n => x i μ)

omit [NeZero d] in
private theorem continuous_splitFirst {n m : ℕ} :
    Continuous (splitFirst n m : NPointDomain d (n + m) → NPointDomain d n) := by
  apply continuous_pi
  intro i
  simpa [splitFirst] using
    (continuous_apply (Fin.castAdd m i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.castAdd m i))

omit [NeZero d] in
private theorem continuous_splitLast {n m : ℕ} :
    Continuous (splitLast n m : NPointDomain d (n + m) → NPointDomain d m) := by
  apply continuous_pi
  intro i
  simpa [splitLast] using
    (continuous_apply (Fin.natAdd n i) :
      Continuous fun x : NPointDomain d (n + m) => x (Fin.natAdd n i))

/-- If a head test is supported in a positive-time barrier `0 < τ_head < τ` and the
tail test is supported strictly after that barrier with increasing times, then
`prependField` lands in the ordered positive-time region. This is the basic
support geometry behind interleaved OS insertions. -/
theorem SchwartzMap.prependField_tsupport_subset_orderedPositiveTimeRegion_of_barrier
    {n : ℕ} (τ : ℝ) (f : SchwartzSpacetime d) (g : SchwartzNPoint d n)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0 ∧ x 0 < τ})
    (hg : tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | ∀ i : Fin n, τ < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0}) :
    tsupport (((SchwartzMap.prependField f g : SchwartzNPoint d (n + 1)) :
      NPointDomain d (n + 1) → ℂ)) ⊆ OrderedPositiveTimeRegion d (n + 1) := by
  let A : Set (NPointDomain d (n + 1)) := {x | 0 < x 0 0 ∧ x 0 0 < τ}
  let B : Set (NPointDomain d (n + 1)) :=
    {x | ∀ i : Fin n, τ < x i.succ 0 ∧ ∀ j : Fin n, i < j → x i.succ 0 < x j.succ 0}
  have hA :
      tsupport (fun x : NPointDomain d (n + 1) => f (x 0)) ⊆ A := by
    intro x hx
    exact hf <|
      tsupport_precomp_subset
        (f := (f : SpacetimeDim d → ℂ))
        (h := fun y : NPointDomain d (n + 1) => y 0)
        (by simpa using (continuous_apply (0 : Fin (n + 1)))) hx
  have hB :
      tsupport (fun x : NPointDomain d (n + 1) => g (fun i : Fin n => x i.succ)) ⊆ B := by
    intro x hx
    exact hg <|
      tsupport_precomp_subset
        (f := (g : NPointDomain d n → ℂ))
        (h := fun y : NPointDomain d (n + 1) => fun i : Fin n => y i.succ)
        (by
          apply continuous_pi
          intro i
          simpa using (continuous_apply i.succ :
            Continuous (fun y : NPointDomain d (n + 1) => y i.succ))) hx
  have hsupport :
      tsupport (((SchwartzMap.prependField f g : SchwartzNPoint d (n + 1)) :
          NPointDomain d (n + 1) → ℂ)) ⊆ A ∩ B := by
    intro x hx
    have hxprod :
        x ∈ tsupport (fun y : NPointDomain d (n + 1) =>
          f (y 0) * g (fun i : Fin n => y i.succ)) := by
      simpa [SchwartzMap.prependField_apply] using hx
    refine ⟨hA ((tsupport_mul_subset_left
      (f := fun y : NPointDomain d (n + 1) => f (y 0))
      (g := fun y : NPointDomain d (n + 1) => g (fun i : Fin n => y i.succ))) hxprod), ?_⟩
    exact hB ((tsupport_mul_subset_right
      (f := fun y : NPointDomain d (n + 1) => f (y 0))
      (g := fun y : NPointDomain d (n + 1) => g (fun i : Fin n => y i.succ))) hxprod)
  intro x hx
  rcases hsupport hx with ⟨hxA, hxB⟩
  have hτ_pos : 0 < τ := lt_trans hxA.1 hxA.2
  intro i
  constructor
  · by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      simpa [A, hi] using hxA.1
    · let i' : Fin n := ⟨i.val - 1, by omega⟩
      have hi : i'.succ = i := by
        ext
        simp [i']
        omega
      have hτlt : τ < x i 0 := by
        simpa [B, i', hi] using (hxB i').1
      linarith
  · intro j hij
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hj0 : j.val ≠ 0 := by omega
      let j' : Fin n := ⟨j.val - 1, by omega⟩
      have hj' : j'.succ = j := by
        ext
        simp [j']
        omega
      have hτlt : τ < x j 0 := by
        simpa [B, j', hj'] using (hxB j').1
      have hx0lt : x i 0 < τ := by simpa [A, hi] using hxA.2
      linarith
    · have hj0 : j.val ≠ 0 := by omega
      let i' : Fin n := ⟨i.val - 1, by omega⟩
      let j' : Fin n := ⟨j.val - 1, by omega⟩
      have hi' : i'.succ = i := by
        ext
        simp [i']
        omega
      have hj' : j'.succ = j := by
        ext
        simp [j']
        omega
      have hij' : i' < j' := by
        simp [i', j']
        omega
      simpa [B, i', j', hi', hj'] using (hxB i').2 j' hij'

/-- OS-conjugated tensor products of ordered positive-time test functions are
    automatically zero-diagonal.

    Geometrically, `f.osConj` is supported where all first-block times are
    strictly negative and decreasing, while `g` stays on the ordered positive-time
    region. Hence every configuration in the topological support of
    `(θf̄) ⊗ g` has all time coordinates distinct, so the coincidence locus is
    avoided before taking any derivatives. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hg : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    VanishesToInfiniteOrderOnCoincidence (f.osConjTensorProduct g) := by
  let A : Set (NPointDomain d (n + m)) :=
    { x | splitFirst n m x ∈ OrderedNegativeTimeRegion d n }
  let B : Set (NPointDomain d (n + m)) :=
    { x | splitLast n m x ∈ OrderedPositiveTimeRegion d m }
  have hosConj :
      tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n := by
    intro x hx i
    have hxpre :
        timeReflectionN d x ∈ tsupport (f : NPointDomain d n → ℂ) := by
      exact tsupport_precomp_subset (f := (f : NPointDomain d n → ℂ))
        (h := timeReflectionN d) (continuous_timeReflectionN (d := d))
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _) (fun y : NPointDomain d n =>
          f (timeReflectionN d y))) hx)
    have hpos := hf hxpre
    constructor
    · have : 0 < timeReflectionN d x i 0 := (hpos i).1
      simpa [timeReflectionN, timeReflection] using this
    · intro j hij
      have : timeReflectionN d x i 0 < timeReflectionN d x j 0 := (hpos i).2 j hij
      simpa [timeReflectionN, timeReflection] using this
  have hA :
      tsupport (fun x : NPointDomain d (n + m) => f.osConj (splitFirst n m x)) ⊆ A := by
    intro x hx
    exact hosConj <|
      tsupport_precomp_subset (f := ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        (h := splitFirst n m) (continuous_splitFirst (d := d)) hx
  have hB :
      tsupport (fun x : NPointDomain d (n + m) => g (splitLast n m x)) ⊆ B := by
    intro x hx
    exact hg <|
      tsupport_precomp_subset (f := (g : NPointDomain d m → ℂ))
        (h := splitLast n m) (continuous_splitLast (d := d)) hx
  have hsupport :
      tsupport (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ)) ⊆ A ∩ B := by
    intro x hx
    have hxprod :
        x ∈ tsupport (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
      simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply] using hx
    refine ⟨hA ((tsupport_mul_subset_left (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod), ?_⟩
    exact hB ((tsupport_mul_subset_right (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod)
  have hdisj : Disjoint (A ∩ B) (CoincidenceLocus d (n + m)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxAB hxcoin
    rcases hxAB with ⟨hxA, hxB⟩
    rcases hxcoin with ⟨i, j, hij, hijEq⟩
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hEq0 : splitFirst n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, hi_cast, hj_cast] using congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin n => Fin.castAdd m t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitFirst n m x j' 0 < splitFirst n m x i' 0 := (hxA i').2 j' hij'_lt
          exact (lt_irrefl (splitFirst n m x j' 0)) (hEq0 ▸ hlt)
        · have hlt : splitFirst n m x i' 0 < splitFirst n m x j' 0 := (hxA j').2 i' hij'_gt
          exact (lt_irrefl (splitFirst n m x i' 0)) (hEq0.symm ▸ hlt)
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hneg : splitFirst n m x i' 0 < 0 := (hxA i').1
        have hpos : 0 < splitLast n m x j' 0 := (hxB j').1
        have hEq0 : splitFirst n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
    · by_cases hj : j.1 < n
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hpos : 0 < splitLast n m x i' 0 := (hxB i').1
        have hneg : splitFirst n m x j' 0 < 0 := (hxA j').1
        have hEq0 : splitLast n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hEq0 : splitLast n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin m => Fin.natAdd n t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitLast n m x i' 0 < splitLast n m x j' 0 := (hxB i').2 j' hij'_lt
          exact (lt_irrefl (splitLast n m x i' 0)) (hEq0 ▸ hlt)
        · have hlt : splitLast n m x j' 0 < splitLast n m x i' 0 := (hxB j').2 i' hij'_gt
          exact (lt_irrefl (splitLast n m x j' 0)) (hEq0.symm ▸ hlt)
  exact VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
    (f := f.osConjTensorProduct g) (hdisj.mono_left hsupport)

end TimeReflectSchwartz

end
