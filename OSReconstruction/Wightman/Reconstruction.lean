/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Topology.UniformSpace.Completion
import OSReconstruction.Wightman.WightmanAxioms
import OSReconstruction.Wightman.SchwartzTensorProduct

/-!
# Wightman Reconstruction Theorem

This file provides the framework for the Wightman reconstruction theorem, which
establishes that a collection of Wightman functions satisfying appropriate properties
uniquely determines a Wightman QFT (up to unitary equivalence).

## Main Definitions

* `WightmanFunctions` - A collection of n-point functions satisfying Wightman properties
* `WightmanReconstruction` - The reconstruction of a Wightman QFT from functions
* `ReconstructionTheorem` - The main theorem statement

## Mathematical Background

The Wightman reconstruction theorem [Wightman, 1956; Streater-Wightman, 1964] states:

Given a collection of distributions W_n : 𝒮(ℝ^{n(d+1)}) → ℂ satisfying:
1. **Temperedness**: Each W_n is a tempered distribution
2. **Covariance**: W_n transforms appropriately under Poincaré transformations
3. **Spectrum condition**: Reflected in the support of the Fourier transform
4. **Locality**: Symmetry under exchange of spacelike-separated arguments
5. **Positive definiteness**: A sesquilinear form condition

Then there exists a unique (up to unitary equivalence) Wightman QFT with these
functions as its n-point functions.

## References

* Wightman, "Quantum field theory in terms of vacuum expectation values" (1956)
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Wightman-Gårding, "Fields as operator-valued distributions" (1965)
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View", Chapter 19
-/

noncomputable section

open scoped SchwartzMap
open Topology

variable (d : ℕ) [NeZero d]

-- Many inner product theorems only use d : ℕ, not [NeZero d].
-- Suppress the auto-inclusion warning for these infrastructure lemmas.
set_option linter.unusedSectionVars false

/-! ### Properties of Wightman Functions -/

/-- The space of n copies of spacetime for n-point functions -/
abbrev NPointDomain (d n : ℕ) := Fin n → SpacetimeDim d

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPoint (d n : ℕ) := SchwartzMap (NPointDomain d n) ℂ

/-! #### Actions on test functions

The Poincaré group acts on test functions by (g · f)(x) = f(g⁻¹ · x).
For the Schwartz space, we need to verify that these actions preserve the Schwartz class.
This is true but requires substantial analysis infrastructure. We define the actions
on plain functions and note where Schwartz preservation would be needed. -/

/-- Translation action on n-point functions (underlying function level) -/
def translateNPointFun (a : SpacetimeDim d) (f : NPointDomain d n → ℂ) : NPointDomain d n → ℂ :=
  fun x => f (fun i => x i - a)

/-- Lorentz action on n-point functions (underlying function level) -/
def lorentzNPointFun (Λ : LorentzGroup d) (f : NPointDomain d n → ℂ) : NPointDomain d n → ℂ :=
  fun x => f (fun i => Matrix.mulVec Λ⁻¹.val (x i))

/-- Permutation action on n-point functions -/
def permuteNPointFun (σ : Equiv.Perm (Fin n)) (f : NPointDomain d n → ℂ) : NPointDomain d n → ℂ :=
  fun x => f (fun i => x (σ i))

/-- Translation invariance: W_n(x₁+a, ..., xₙ+a) = W_n(x₁, ..., xₙ) for all translations a.

    At the distribution level: W_n(τ_{-a} f) = W_n(f) where (τ_a f)(x) = f(x - a).

    For distributions, this means ∂W_n/∂x_i^μ + ∂W_n/∂x_j^μ = 0 for all i,j,μ,
    i.e., W_n depends only on coordinate differences ξ_i = x_{i+1} - x_i.

    Concretely: W_n can be written as a distribution in n-1 difference variables. -/
def IsTranslationInvariantWeak (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  -- W_n is translation-invariant: for any translation a and any two Schwartz functions
  -- f, g such that g(x) = f(x₁+a,...,xₙ+a), we have W_n(f) = W_n(g).
  -- This avoids needing to construct the translated Schwartz function.
  ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
    (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => x i + a)) →
    W n f = W n g

/-- Lorentz covariance: W_n(Λx₁, ..., Λxₙ) = W_n(x₁, ..., xₙ) for all Λ ∈ O(1,d).

    For scalar fields, the Wightman functions are Lorentz invariant.
    For fields with spin s, there would be a transformation matrix D^{(s)}(Λ).

    At the distribution level: W_n(Λ⁻¹ · f) = W_n(f) where (Λ · f)(x) = f(Λ⁻¹x).

    We express this as invariance under the action of the Lorentz group on n-point
    configurations. -/
def IsLorentzCovariantWeak (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  -- For scalar fields: W_n is Lorentz invariant.
  -- For any Λ ∈ O(1,d) and Schwartz functions f, g such that g(x) = f(Λ⁻¹x₁,...,Λ⁻¹xₙ),
  -- we have W_n(f) = W_n(g). Avoids constructing the Lorentz-transformed Schwartz function.
  ∀ (n : ℕ) (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
    (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
    W n f = W n g

/-- Local commutativity condition for Wightman functions.

    For a collection of n-point functions W_n, local commutativity means:
    When points x_i and x_j are spacelike separated, swapping them in W_n
    doesn't change the value (for bosonic fields; fermionic fields get a sign).

    The precise condition is:
    W_n(..., x_i, ..., x_j, ...) = W_n(..., x_j, ..., x_i, ...)
    when (x_i - x_j)² > 0 (spacelike separation in mostly positive signature).

    At the distribution level, this is expressed via test functions with
    spacelike-separated supports: if supp(f) and supp(g) are spacelike separated,
    then W₂(f ⊗ g) = W₂(g ⊗ f). -/
def IsLocallyCommutativeWeak (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  -- For Schwartz functions f, g where g is the swap of coordinates i, j in f,
  -- and the supports of f have spacelike-separated i-th and j-th arguments,
  -- we have W_n(f) = W_n(g). Avoids constructing the swapped Schwartz function.
  ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n),
    (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
    (∀ x : NPointDomain d n, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
    W n f = W n g

/-! ### Positive Definiteness -/

/-- The Borchers class of test function sequences.

    A Borchers sequence is a finitely supported sequence of Schwartz n-point functions.
    The n-th component f_n ∈ S(ℝ^{n(d+1)}, ℂ) is a test function on n copies of spacetime.

    The `funcs` field is indexed by all n ∈ ℕ, with `bound_spec` ensuring all
    components beyond `bound` are zero. This simplifies algebraic operations
    (addition, scalar multiplication, etc.) compared to a dependent-type formulation. -/
structure BorchersSequence (d : ℕ) where
  /-- For each n, a test function on n copies of spacetime -/
  funcs : (n : ℕ) → SchwartzNPoint d n
  /-- A bound on the support: all components beyond this are zero -/
  bound : ℕ
  /-- All components beyond the bound are zero -/
  bound_spec : ∀ n, bound < n → funcs n = 0

/-! ### Borchers Sequence Algebra -/

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

end BorchersSequence

/-! ### Wightman Inner Product -/

/-- The inner product induced by Wightman functions on Borchers sequences.

    ⟨F, G⟩ = Σ_{n ≤ N_F} Σ_{m ≤ N_G} W_{n+m}(f*_n ⊗ g_m)

    where:
    - f*_n is the Borchers involution: f*_n(x₁,...,xₙ) = conj(f_n(xₙ,...,x₁))
    - f*_n ⊗ g_m is the external tensor product in SchwartzNPoint d (n+m)
    - W_{n+m} evaluates the (n+m)-point function on the tensor product

    The Borchers involution includes both conjugation AND argument reversal. This is
    essential for the Hermiticity of the inner product: ⟨F, G⟩ = conj(⟨G, F⟩).

    Since `F.funcs n = 0` for `n > F.bound` and `G.funcs m = 0` for `m > G.bound`,
    the sum is effectively finite.

    Reference: Streater-Wightman, "PCT, Spin and Statistics", §3.4 -/
def WightmanInnerProduct (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (F G : BorchersSequence d) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      W (n + m) ((F.funcs n).conjTensorProduct (G.funcs m))

/-! ### Inner Product Range Extension

The key technical lemma: extending the summation range beyond the bound doesn't
change the inner product, because extra terms have zero Schwartz functions and
W is linear (W_k(0) = 0). This enables proving sesquilinearity when adding
sequences with different bounds. -/

/-- The inner product with explicit summation bounds. -/
def WightmanInnerProductN (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (F G : BorchersSequence d) (N₁ N₂ : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N₁,
    ∑ m ∈ Finset.range N₂,
      W (n + m) ((F.funcs n).conjTensorProduct (G.funcs m))

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

/-! ### Inner Product Sesquilinearity -/

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

/-- The inner product with zero on the left vanishes. -/
theorem WightmanInnerProduct_zero_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (G : BorchersSequence d) :
    WightmanInnerProduct d W (0 : BorchersSequence d) G = 0 := by
  unfold WightmanInnerProduct
  apply Finset.sum_eq_zero; intro n _
  apply Finset.sum_eq_zero; intro m _
  simp [(hlin _).map_zero]

/-- The inner product with zero on the right vanishes. -/
theorem WightmanInnerProduct_zero_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F : BorchersSequence d) :
    WightmanInnerProduct d W F (0 : BorchersSequence d) = 0 := by
  unfold WightmanInnerProduct
  apply Finset.sum_eq_zero; intro n _
  apply Finset.sum_eq_zero; intro m _
  simp [(hlin _).map_zero]

/-- The inner product depends only on the funcs of the right argument. -/
theorem WightmanInnerProduct_congr_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F : BorchersSequence d) (G₁ G₂ : BorchersSequence d)
    (hg : ∀ n, G₁.funcs n = G₂.funcs n) :
    WightmanInnerProduct d W F G₁ = WightmanInnerProduct d W F G₂ := by
  rw [WightmanInnerProduct_eq_extended d W hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_left _ _)),
      WightmanInnerProduct_eq_extended d W hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_right _ _))]
  simp only [WightmanInnerProductN]
  congr 1; ext n; congr 1; ext m; rw [hg m]

/-- The inner product depends only on the funcs of the left argument. -/
theorem WightmanInnerProduct_congr_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F₁ F₂ : BorchersSequence d) (G : BorchersSequence d)
    (hf : ∀ n, F₁.funcs n = F₂.funcs n) :
    WightmanInnerProduct d W F₁ G = WightmanInnerProduct d W F₂ G := by
  rw [WightmanInnerProduct_eq_extended d W hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_left _ _)) le_rfl,
      WightmanInnerProduct_eq_extended d W hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_right _ _)) le_rfl]
  simp only [WightmanInnerProductN]
  congr 1; ext n; congr 1; ext m; rw [hf n]

/-- The inner product is anti-additive (negation) in the first argument. -/
theorem WightmanInnerProduct_neg_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W (-F) G = -(WightmanInnerProduct d W F G) := by
  simp only [WightmanInnerProduct, BorchersSequence.neg_funcs, BorchersSequence.neg_bound]
  simp_rw [SchwartzMap.conjTensorProduct_neg_left,
    show ∀ k (x : SchwartzNPoint d k), W k (-x) = -(W k x) from
      fun k x => (hlin k).map_neg x]
  simp [Finset.sum_neg_distrib]

/-- The inner product is anti-additive (negation) in the second argument. -/
theorem WightmanInnerProduct_neg_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W F (-G) = -(WightmanInnerProduct d W F G) := by
  simp only [WightmanInnerProduct, BorchersSequence.neg_funcs, BorchersSequence.neg_bound]
  simp_rw [SchwartzMap.conjTensorProduct_neg_right,
    show ∀ k (x : SchwartzNPoint d k), W k (-x) = -(W k x) from
      fun k x => (hlin k).map_neg x]
  simp [Finset.sum_neg_distrib]

/-- The inner product is subtractive in the second argument. -/
theorem WightmanInnerProduct_sub_right (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G₁ G₂ : BorchersSequence d) :
    WightmanInnerProduct d W F (G₁ - G₂) =
    WightmanInnerProduct d W F G₁ - WightmanInnerProduct d W F G₂ := by
  -- G₁ - G₂ and G₁ + (-G₂) have the same funcs pointwise
  rw [WightmanInnerProduct_congr_right d W hlin F (G₁ - G₂) (G₁ + (-G₂))
    (fun n => by simp [sub_eq_add_neg])]
  rw [WightmanInnerProduct_add_right d W hlin F G₁ (-G₂),
      WightmanInnerProduct_neg_right d W hlin F G₂]
  ring

/-- The inner product is subtractive in the first argument. -/
theorem WightmanInnerProduct_sub_left (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F₁ F₂ G : BorchersSequence d) :
    WightmanInnerProduct d W (F₁ - F₂) G =
    WightmanInnerProduct d W F₁ G - WightmanInnerProduct d W F₂ G := by
  rw [WightmanInnerProduct_congr_left d W hlin (F₁ - F₂) (F₁ + (-F₂)) G
    (fun n => by simp [sub_eq_add_neg])]
  rw [WightmanInnerProduct_add_left d W hlin F₁ (-F₂) G,
      WightmanInnerProduct_neg_left d W hlin F₂ G]
  ring

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

/-! ### Expansion of ⟨F-G, F-G⟩ -/

/-- The setoid condition equals ⟨F-G, F-G⟩: expanding the inner product on the difference. -/
theorem WightmanInnerProduct_expand_diff (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W (F - G) (F - G) =
    WightmanInnerProduct d W F F + WightmanInnerProduct d W G G
    - WightmanInnerProduct d W F G - WightmanInnerProduct d W G F := by
  rw [WightmanInnerProduct_sub_left d W hlin F G (F - G),
      WightmanInnerProduct_sub_right d W hlin F F G,
      WightmanInnerProduct_sub_right d W hlin G F G]
  ring

/-- Positive definiteness of Wightman functions -/
def IsPositiveDefinite (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0

/-- Normalization: W_0 = 1 -/
def IsNormalized (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ f : SchwartzNPoint d 0, W 0 f = f 0

/-! ### Wightman Functions Structure -/

/-- A collection of Wightman functions satisfying all required properties.
    This is the input data for the reconstruction theorem. -/
structure WightmanFunctions (d : ℕ) [NeZero d] where
  /-- The n-point functions as tempered distributions -/
  W : (n : ℕ) → SchwartzNPoint d n → ℂ
  /-- Each W_n is linear -/
  linear : ∀ n, IsLinearMap ℂ (W n)
  /-- Each W_n is continuous (tempered) -/
  tempered : ∀ n, Continuous (W n)
  /-- Normalization -/
  normalized : IsNormalized d W
  /-- Translation invariance (weak form) -/
  translation_invariant : IsTranslationInvariantWeak d W
  /-- Lorentz covariance (weak form) -/
  lorentz_covariant : IsLorentzCovariantWeak d W
  /-- Spectral condition: the Fourier transform of W_n has support in the product
      of forward light cones.

      More precisely, W̃_n(p₁,...,pₙ) (the Fourier transform) vanishes unless
      p₁ + ... + pₖ ∈ V̄₊ for all k = 1,...,n, where V̄₊ is the closed forward cone.

      This is equivalent to the energy-momentum spectrum lying in the forward cone.

      The condition is expressed via analytic continuation: W_n extends to a
      holomorphic function on the forward tube T_n. By the Bargmann-Hall-Wightman
      theorem, this is equivalent to the spectral support condition.

      We require:
      1. Existence of an analytic continuation W_analytic to the forward tube
      2. Holomorphicity (differentiability in each complex variable)
      3. Boundary values recover W_n: as Im(z) → 0⁺ from within the tube,
         W_analytic approaches the distribution W_n in the sense of distributions -/
  spectrum_condition : ∀ (n : ℕ),
    ∃ (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- Holomorphicity on the forward tube (DifferentiableOn avoids subtype issues)
      DifferentiableOn ℂ W_analytic (ForwardTube d n) ∧
      -- Boundary values: W_analytic recovers W_n as imaginary parts approach zero.
      -- For any test function f and approach direction η with components in V₊,
      -- lim_{ε→0⁺} ∫ W_analytic(x + iεη) f(x) dx = W_n(f)
      -- This is the distributional boundary value condition:
      -- the smeared analytic continuation converges to the Wightman distribution.
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        (∀ k, InOpenForwardCone d (η k)) →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W n f)))
  /-- Local commutativity (weak form) -/
  locally_commutative : IsLocallyCommutativeWeak d W
  /-- Positive definiteness -/
  positive_definite : IsPositiveDefinite d W
  /-- Hermiticity: W_n(f̃) = conj(W_n(f)) where f̃(x₁,...,xₙ) = conj(f(xₙ,...,x₁)).

      This is the standard Hermiticity axiom for Wightman functions at the distribution level:
        W_n(x₁,...,xₙ)* = W_n(xₙ,...,x₁)

      In the weak formulation: if g(x) = conj(f(rev(x))) for all x, then W_n(g) = conj(W_n(f)).
      Here `Fin.rev` reverses the argument order: (x₁,...,xₙ) ↦ (xₙ,...,x₁). -/
  hermitian : ∀ (n : ℕ) (f g : SchwartzNPoint d n),
    (∀ x : NPointDomain d n, g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
    W n g = starRingEnd ℂ (W n f)

/-! ### Inner Product Hermiticity and Cauchy-Schwarz -/

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

    This follows from the Hermiticity axiom on Wightman functions:
    W_n(f̃) = conj(W_n(f)) where f̃(x) = conj(f(rev(x))).

    The proof has three steps:
    1. Pull conjugation through the double sum
    2. Apply the Hermiticity axiom to each term: conj(W_k(h)) = W_k(borchersConj(h))
    3. Use the reversal identity to identify borchersConj(g* ⊗ f) with f* ⊗ g
       (up to the n+m ↔ m+n type transport)
    4. Swap summation indices -/
theorem WightmanInnerProduct_hermitian {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (F G : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W F G = starRingEnd ℂ (WightmanInnerProduct d Wfn.W G F) := by
  simp only [WightmanInnerProduct, map_sum]
  -- Swap the summation order in the LHS via sum_comm
  rw [Finset.sum_comm]
  -- After sum_comm + congr/ext, the goal for each (m, n) pair is:
  -- W (m+n) (F_m.conjTP G_n) = conj(W (n+m) (G_n.conjTP F_m))
  congr 1; ext n; congr 1; ext m
  -- Step 1: Use Hermiticity axiom to rewrite conj(W(n+m)(h)) = W(n+m)(h.borchersConj)
  rw [← Wfn.hermitian (n + m) ((G.funcs n).conjTensorProduct (F.funcs m))
    (((G.funcs n).conjTensorProduct (F.funcs m)).borchersConj) (fun _ => rfl)]
  -- Goal: W (m+n) (F_m.conjTP G_n) = W (n+m) ((G_n.conjTP F_m).borchersConj)
  -- Step 2: Transport via m+n = n+m and the reversal identity
  exact W_eq_of_cast Wfn.W (m + n) (n + m) (Nat.add_comm m n)
    ((F.funcs m).conjTensorProduct (G.funcs n))
    (((G.funcs n).conjTensorProduct (F.funcs m)).borchersConj)
    (fun x => conjTP_eq_borchersConj_conjTP (F.funcs m) (G.funcs n) x)

/-- If at² + bt ≥ 0 for all real t, with a ≥ 0, then b = 0.
    This is the key algebraic lemma for the Cauchy-Schwarz argument. -/
private theorem quadratic_nonneg_linear_zero
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

/-- Quadratic expansion: ⟨X + tY, X + tY⟩.re = ⟨X,X⟩.re + 2t·Re⟨X,Y⟩ + t²·⟨Y,Y⟩.re -/
private theorem inner_product_quadratic_re {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) (X Y : BorchersSequence d) (t : ℝ) :
    (WightmanInnerProduct d Wfn.W (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re =
    (WightmanInnerProduct d Wfn.W X X).re +
    2 * (WightmanInnerProduct d Wfn.W X Y).re * t +
    (WightmanInnerProduct d Wfn.W Y Y).re * t ^ 2 := by
  have hlin := Wfn.linear
  -- Expand using sesquilinearity + Hermiticity
  rw [WightmanInnerProduct_add_left d Wfn.W hlin,
      WightmanInnerProduct_add_right d Wfn.W hlin X,
      WightmanInnerProduct_add_right d Wfn.W hlin ((↑t : ℂ) • Y),
      WightmanInnerProduct_smul_right d Wfn.W hlin _ X,
      WightmanInnerProduct_smul_left d Wfn.W hlin _ Y,
      WightmanInnerProduct_smul_left d Wfn.W hlin _ Y,
      WightmanInnerProduct_smul_right d Wfn.W hlin _ Y,
      WightmanInnerProduct_hermitian Wfn Y X]
  -- Simplify conj(↑t) = ↑t for real t, then distribute .re
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- If ⟨X, X⟩.re = 0 (X is null), then ⟨X, Y⟩ = 0 for all Y.

    Proof uses the quadratic argument with Hermiticity:
    1. For real t: ⟨X+tY, X+tY⟩.re = 2t·Re(⟨X,Y⟩) + t²·⟨Y,Y⟩.re ≥ 0 → Re(⟨X,Y⟩) = 0
    2. For I•Y: ⟨X, I•Y⟩.re = -Im(⟨X,Y⟩) = 0 → Im(⟨X,Y⟩) = 0
    3. Reconstruct: ⟨X,Y⟩ = 0 -/
theorem null_inner_product_zero {d : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d)
    (X Y : BorchersSequence d)
    (hX : (WightmanInnerProduct d Wfn.W X X).re = 0) :
    WightmanInnerProduct d Wfn.W X Y = 0 := by
  have hlin := Wfn.linear
  set w := WightmanInnerProduct d Wfn.W X Y with hw_def
  -- Step 1: Show w.re = 0 using the quadratic argument with real scalars
  have hre : w.re = 0 := by
    -- For all real t: ⟨X + (↑t)•Y, X + (↑t)•Y⟩.re ≥ 0
    -- After expansion: this equals ⟨Y,Y⟩.re * t² + 2 * w.re * t
    -- (using ⟨X,X⟩.re = 0, Hermiticity, and (z + conj z).re = 2*z.re)
    -- By quadratic_nonneg_linear_zero: 2 * w.re = 0
    apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
    rw [mul_zero]
    apply quadratic_nonneg_linear_zero (WightmanInnerProduct d Wfn.W Y Y).re
    · exact Wfn.positive_definite Y
    · intro t
      rw [show (WightmanInnerProduct d Wfn.W Y Y).re * t ^ 2 + 2 * w.re * t =
        (WightmanInnerProduct d Wfn.W (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re from by
          rw [inner_product_quadratic_re Wfn X Y t, hX]; ring]
      exact Wfn.positive_definite _
  -- Step 2: Show w.im = 0 by applying step 1 to I•Y
  have him : w.im = 0 := by
    -- ⟨X, I•Y⟩ = I * w by linearity, and (I * w).re = -w.im
    have hIw : WightmanInnerProduct d Wfn.W X (Complex.I • Y) = Complex.I * w := by
      rw [WightmanInnerProduct_smul_right d Wfn.W hlin Complex.I X Y]
    -- Apply the same quadratic argument to Z = I•Y:
    -- ⟨X, Z⟩.re = (I*w).re = 0*w.re - 1*w.im = -w.im
    -- From the quadratic argument: ⟨X, Z⟩.re = 0, so w.im = 0
    have hIw_re : (Complex.I * w).re = -w.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    -- Apply the quadratic argument to X and Z = I•Y
    have hre_Z : (WightmanInnerProduct d Wfn.W X (Complex.I • Y)).re = 0 := by
      apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
      rw [mul_zero]
      apply quadratic_nonneg_linear_zero (WightmanInnerProduct d Wfn.W (Complex.I • Y) (Complex.I • Y)).re
      · exact Wfn.positive_definite _
      · intro t
        rw [show (WightmanInnerProduct d Wfn.W (Complex.I • Y) (Complex.I • Y)).re * t ^ 2 +
          2 * (WightmanInnerProduct d Wfn.W X (Complex.I • Y)).re * t =
          (WightmanInnerProduct d Wfn.W (X + (↑t : ℂ) • (Complex.I • Y))
            (X + (↑t : ℂ) • (Complex.I • Y))).re from by
              rw [inner_product_quadratic_re Wfn X (Complex.I • Y) t, hX]; ring]
        exact Wfn.positive_definite _
    rw [hIw] at hre_Z; rw [hIw_re] at hre_Z; linarith
  -- Step 3: Reconstruct w = 0 from w.re = 0 and w.im = 0
  exact Complex.ext hre him

/-! ### The Reconstruction -/

/-- The GNS equivalence relation on Borchers sequences.

    F ~ G iff ‖F - G‖² = 0, which by sesquilinearity expands to:
    Re(⟨F,F⟩ + ⟨G,G⟩ - ⟨F,G⟩ - ⟨G,F⟩) = 0.

    This is the correct GNS quotient: we identify sequences whose difference
    has zero norm, not merely those that individually have zero norm. -/
def borchersSetoid {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) :
    Setoid (BorchersSequence d) where
  r F G :=
    (WightmanInnerProduct d Wfn.W F F + WightmanInnerProduct d Wfn.W G G
      - WightmanInnerProduct d Wfn.W F G - WightmanInnerProduct d Wfn.W G F).re = 0
  iseqv := {
    refl := fun F => by simp
    symm := fun {F G} h => by
      -- The expression is symmetric: swapping F↔G gives the same value
      have : (WightmanInnerProduct d Wfn.W G G + WightmanInnerProduct d Wfn.W F F
        - WightmanInnerProduct d Wfn.W G F - WightmanInnerProduct d Wfn.W F G).re =
        (WightmanInnerProduct d Wfn.W F F + WightmanInnerProduct d Wfn.W G G
        - WightmanInnerProduct d Wfn.W F G - WightmanInnerProduct d Wfn.W G F).re := by
        congr 1; ring
      rw [this]; exact h
    trans := fun {F G H} hFG hGH => by
      -- Transitivity: if ‖F-G‖²=0 and ‖G-H‖²=0, then ‖F-H‖²=0
      -- Uses the parallelogram trick with positive definiteness
      have hlin := Wfn.linear
      -- Suffices to show ⟨F-H, F-H⟩.re = 0
      suffices h : (WightmanInnerProduct d Wfn.W (F - H) (F - H)).re = 0 by
        rw [WightmanInnerProduct_expand_diff d Wfn.W hlin F H] at h; exact h
      -- (F-H).funcs = ((F-G)+(G-H)).funcs pointwise
      have hfuncs : ∀ n, (F - H).funcs n = ((F - G) + (G - H)).funcs n :=
        fun n => by simp [sub_add_sub_cancel]
      -- Replace ⟨F-H, F-H⟩ with ⟨(F-G)+(G-H), (F-G)+(G-H)⟩
      have hkey : WightmanInnerProduct d Wfn.W (F - H) (F - H) =
          WightmanInnerProduct d Wfn.W ((F - G) + (G - H)) ((F - G) + (G - H)) :=
        (WightmanInnerProduct_congr_left d Wfn.W hlin _ _ _ hfuncs).trans
          (WightmanInnerProduct_congr_right d Wfn.W hlin _ _ _ hfuncs)
      rw [hkey]
      -- Hypotheses: ⟨F-G, F-G⟩.re = 0 and ⟨G-H, G-H⟩.re = 0
      have hXX : (WightmanInnerProduct d Wfn.W (F - G) (F - G)).re = 0 := by
        rw [WightmanInnerProduct_expand_diff d Wfn.W hlin F G]; exact hFG
      have hYY : (WightmanInnerProduct d Wfn.W (G - H) (G - H)).re = 0 := by
        rw [WightmanInnerProduct_expand_diff d Wfn.W hlin G H]; exact hGH
      -- Positive definiteness of (F-G)+(G-H) and (F-G)-(G-H)
      have hpos1 := Wfn.positive_definite ((F - G) + (G - H))
      have hpos2 := Wfn.positive_definite ((F - G) - (G - H))
      -- Expand ⟨A+B, A+B⟩ = ⟨A,A⟩ + ⟨A,B⟩ + (⟨B,A⟩ + ⟨B,B⟩)
      have hexpand : ∀ A B : BorchersSequence d,
          WightmanInnerProduct d Wfn.W (A + B) (A + B) =
          WightmanInnerProduct d Wfn.W A A + WightmanInnerProduct d Wfn.W A B +
          (WightmanInnerProduct d Wfn.W B A + WightmanInnerProduct d Wfn.W B B) := by
        intro A B
        rw [WightmanInnerProduct_add_left d Wfn.W hlin A B,
            WightmanInnerProduct_add_right d Wfn.W hlin A A B,
            WightmanInnerProduct_add_right d Wfn.W hlin B A B]
      rw [hexpand] at hpos1 ⊢
      -- Expand ⟨A-B, A-B⟩ = ⟨A,A⟩ + ⟨B,B⟩ - ⟨A,B⟩ - ⟨B,A⟩
      rw [WightmanInnerProduct_expand_diff d Wfn.W hlin (F - G) (G - H)] at hpos2
      -- Distribute .re over + and -
      simp only [Complex.add_re, Complex.sub_re] at *
      -- From hXX, hYY, hpos1, hpos2: linarith concludes
      -- hpos1: cross ≥ 0, hpos2: -cross ≥ 0, so cross = 0
      linarith
  }

/-- The pre-Hilbert space constructed from Wightman functions via the GNS construction.
    Vectors are equivalence classes of Borchers sequences modulo the null space
    N = {F : ⟨F, F⟩ = 0}. Two sequences are identified if their difference is null. -/
def PreHilbertSpace {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) : Type :=
  Quotient (borchersSetoid Wfn)

/-- The inner product on the pre-Hilbert space -/
def PreHilbertSpace.innerProduct {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) :
    PreHilbertSpace Wfn → PreHilbertSpace Wfn → ℂ :=
  Quotient.lift₂ (WightmanInnerProduct d Wfn.W) (by
    -- Quotient.lift₂: ha : a₁ ≈ b₁, hb : a₂ ≈ b₂, goal: IP a₁ a₂ = IP b₁ b₂
    intro a₁ a₂ b₁ b₂ ha hb
    have hlin := Wfn.linear
    -- Step 1: a₁ ≈ b₁ means ⟨a₁-b₁, a₁-b₁⟩.re = 0
    have ha_null : (WightmanInnerProduct d Wfn.W (a₁ - b₁) (a₁ - b₁)).re = 0 := by
      rw [WightmanInnerProduct_expand_diff d Wfn.W hlin]; exact ha
    -- Step 2: ⟨a₁, G⟩ = ⟨b₁, G⟩ for all G
    have ha_eq : ∀ G, WightmanInnerProduct d Wfn.W a₁ G = WightmanInnerProduct d Wfn.W b₁ G := by
      intro G
      have h := null_inner_product_zero Wfn (a₁ - b₁) G ha_null
      rwa [WightmanInnerProduct_sub_left d Wfn.W hlin, sub_eq_zero] at h
    -- Step 3: a₂ ≈ b₂ means ⟨a₂-b₂, a₂-b₂⟩.re = 0
    have hb_null : (WightmanInnerProduct d Wfn.W (a₂ - b₂) (a₂ - b₂)).re = 0 := by
      rw [WightmanInnerProduct_expand_diff d Wfn.W hlin]; exact hb
    -- Step 4: ⟨F, a₂⟩ = ⟨F, b₂⟩ via Hermiticity + null
    have hb_eq : ∀ F, WightmanInnerProduct d Wfn.W F a₂ = WightmanInnerProduct d Wfn.W F b₂ := by
      intro F
      have h := null_inner_product_zero Wfn (a₂ - b₂) F hb_null
      rw [WightmanInnerProduct_sub_left d Wfn.W hlin, sub_eq_zero] at h
      -- h : ⟨a₂, F⟩ = ⟨b₂, F⟩. Use Hermiticity to swap.
      rw [WightmanInnerProduct_hermitian Wfn F a₂, WightmanInnerProduct_hermitian Wfn F b₂, h]
    -- Combine: IP a₁ a₂ = IP b₁ a₂ = IP b₁ b₂
    rw [ha_eq a₂, hb_eq b₁])

/-- The pre-Hilbert space from the GNS construction: BorchersSequence / NullSpace.

    This is the quotient of Borchers sequences by the null space of the Wightman
    inner product. To obtain the actual Hilbert space (a complete inner product space),
    one would need to:
    1. Equip this type with a UniformSpace/MetricSpace structure from the inner product
    2. Take the Cauchy completion using Mathlib's `UniformSpace.Completion`
    3. Show the inner product extends by continuity to the completion

    For the reconstruction theorem, the pre-Hilbert space suffices to define
    the field operators and verify the Wightman axioms on the dense domain. -/
def ReconstructedPreHilbertSpace {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d) : Type :=
  PreHilbertSpace Wfn

/-! ### Field Operators -/

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

/-- The vacuum vector in the reconstructed Hilbert space.
    The vacuum Borchers sequence has f_0 = 1 (constant function), f_n = 0 for n ≥ 1. -/
def vacuum : PreHilbertSpace Wfn :=
  Quotient.mk _ (vacuumSequence (d := d))

/-- Convert a spacetime test function to a 1-point Schwartz function.
    Uses the equivalence SpacetimeDim d ≃ (Fin 1 → SpacetimeDim d).
    Composing f with the projection (Fin 1 → SpacetimeDim d) → SpacetimeDim d
    preserves the Schwartz class because the projection is a continuous linear equivalence. -/
def schwartzToOnePoint (f : SchwartzSpacetime d) : SchwartzNPoint d 1 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)) f

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

/-- The field operator action is componentwise linear: subtraction. -/
theorem fieldOperatorAction_funcs_sub (f : SchwartzSpacetime d) (F G : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction f (F - G)).funcs n = (fieldOperatorAction f F - fieldOperatorAction f G).funcs n := by
  cases n with
  | zero => simp
  | succ k => simp [SchwartzMap.prependField_sub_right]

/-- Per-term adjoint identity: W_{(n+1)+m}((prependField f fn).conjTP gm) =
    W_{n+(m+1)}(fn.conjTP (prependField f̄ gm)). Both evaluate the Wightman function
    on pointwise-equal test functions (up to Fin.cast and mul_comm in ℂ). -/
private theorem adjoint_term_eq (n m : ℕ) (f : SchwartzSpacetime d)
    (fn : SchwartzNPoint d n) (gm : SchwartzNPoint d m) :
    Wfn.W ((n + 1) + m) ((SchwartzMap.prependField f fn).conjTensorProduct gm) =
    Wfn.W (n + (m + 1)) (fn.conjTensorProduct (SchwartzMap.prependField (SchwartzMap.conj f) gm)) := by
  apply W_eq_of_cast Wfn.W _ _ (by omega)
  intro x
  simp only [SchwartzMap.conjTensorProduct_apply, SchwartzMap.prependField_apply,
    SchwartzMap.conj_apply, splitFirst, splitLast, map_mul]
  have hf_arg : x (Fin.castAdd m (Fin.rev (0 : Fin (n + 1)))) =
      x (Fin.cast (by omega : n + (m + 1) = (n + 1) + m) (Fin.natAdd n (0 : Fin (m + 1)))) := by
    congr 1
  have hfn_args : (fun i : Fin n => x (Fin.castAdd m (Fin.rev (Fin.succ i)))) =
      (fun i : Fin n => x (Fin.cast (by omega : n + (m + 1) = (n + 1) + m)
        (Fin.castAdd (m + 1) (Fin.rev i)))) := by
    ext i; congr 1; ext; simp [Fin.val_rev, Fin.val_castAdd, Fin.val_succ, Fin.val_cast]
  have hgm_args : (fun j : Fin m => x (Fin.natAdd (n + 1) j)) =
      (fun j : Fin m => x (Fin.cast (by omega : n + (m + 1) = (n + 1) + m)
        (Fin.natAdd n (Fin.succ j)))) := by
    ext j; congr 1; ext; simp [Fin.val_natAdd, Fin.val_succ, Fin.val_cast]; omega
  simp only [hf_arg, hfn_args]
  unfold splitLast
  rw [hgm_args]
  ring

/-- The adjoint relation for field operators: ⟨φ(f)F, G⟩ = ⟨F, φ(f̄)G⟩ -/
theorem field_adjoint (f : SchwartzSpacetime d) (F G : BorchersSequence d) :
    WightmanInnerProduct d Wfn.W (fieldOperatorAction f F) G =
    WightmanInnerProduct d Wfn.W F (fieldOperatorAction (SchwartzMap.conj f) G) := by
  set S := ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      Wfn.W ((n + 1) + m) ((SchwartzMap.prependField f (F.funcs n)).conjTensorProduct (G.funcs m))
  have hLHS : WightmanInnerProduct d Wfn.W (fieldOperatorAction f F) G = S := by
    simp only [WightmanInnerProduct, fieldOperatorAction_bound]
    rw [show F.bound + 1 + 1 = (F.bound + 1) + 1 from rfl, Finset.sum_range_succ']
    simp only [fieldOperatorAction_funcs_zero, SchwartzMap.conjTensorProduct_zero_left,
      (Wfn.linear _).map_zero, Finset.sum_const_zero, add_zero,
      fieldOperatorAction_funcs_succ]
    rfl
  have hRHS : WightmanInnerProduct d Wfn.W F (fieldOperatorAction (SchwartzMap.conj f) G) = S := by
    simp only [WightmanInnerProduct, fieldOperatorAction_bound]
    congr 1; ext n
    rw [show G.bound + 1 + 1 = (G.bound + 1) + 1 from rfl, Finset.sum_range_succ']
    simp only [fieldOperatorAction_funcs_zero, SchwartzMap.conjTensorProduct_zero_right,
      (Wfn.linear _).map_zero, add_zero, fieldOperatorAction_funcs_succ]
    congr 1; ext m
    exact (adjoint_term_eq Wfn n m f (F.funcs n) (G.funcs m)).symm
  rw [hLHS, hRHS]

/-- The field operator φ(f) maps null vectors to null vectors. -/
theorem fieldOperator_preserves_null (f : SchwartzSpacetime d) (F : BorchersSequence d)
    (hF : (WightmanInnerProduct d Wfn.W F F).re = 0) :
    (WightmanInnerProduct d Wfn.W (fieldOperatorAction f F) (fieldOperatorAction f F)).re = 0 := by
  have h : WightmanInnerProduct d Wfn.W (fieldOperatorAction f F) (fieldOperatorAction f F) = 0 := by
    rw [field_adjoint Wfn f F (fieldOperatorAction f F)]
    exact null_inner_product_zero Wfn F _ hF
  simp [h]

/-- The field operator is well-defined on the quotient: equivalent Borchers
    sequences map to equivalent sequences under φ(f). -/
theorem fieldOperator_well_defined (f : SchwartzSpacetime d)
    (a b : BorchersSequence d) (hab : borchersSetoid Wfn a b) :
    borchersSetoid Wfn (fieldOperatorAction f a) (fieldOperatorAction f b) := by
  have hab_null : (WightmanInnerProduct d Wfn.W (a - b) (a - b)).re = 0 := by
    rw [WightmanInnerProduct_expand_diff d Wfn.W Wfn.linear a b]; exact hab
  have hpn := fieldOperator_preserves_null Wfn f (a - b) hab_null
  have hfuncs : ∀ n, (fieldOperatorAction f (a - b)).funcs n =
      (fieldOperatorAction f a - fieldOperatorAction f b).funcs n :=
    fieldOperatorAction_funcs_sub f a b
  have hcongr : WightmanInnerProduct d Wfn.W (fieldOperatorAction f a - fieldOperatorAction f b)
      (fieldOperatorAction f a - fieldOperatorAction f b) =
      WightmanInnerProduct d Wfn.W (fieldOperatorAction f (a - b)) (fieldOperatorAction f (a - b)) := by
    exact (WightmanInnerProduct_congr_left d Wfn.W Wfn.linear _ _ _ (fun n => (hfuncs n).symm)).trans
      (WightmanInnerProduct_congr_right d Wfn.W Wfn.linear _ _ _ (fun n => (hfuncs n).symm))
  show (WightmanInnerProduct d Wfn.W (fieldOperatorAction f a) (fieldOperatorAction f a) +
    WightmanInnerProduct d Wfn.W (fieldOperatorAction f b) (fieldOperatorAction f b) -
    WightmanInnerProduct d Wfn.W (fieldOperatorAction f a) (fieldOperatorAction f b) -
    WightmanInnerProduct d Wfn.W (fieldOperatorAction f b) (fieldOperatorAction f a)).re = 0
  rw [← WightmanInnerProduct_expand_diff d Wfn.W Wfn.linear, hcongr]
  exact hpn

/-- The field operator on the pre-Hilbert space -/
def fieldOperator (f : SchwartzSpacetime d) : PreHilbertSpace Wfn → PreHilbertSpace Wfn :=
  Quotient.lift (fun F => Quotient.mk _ (fieldOperatorAction f F)) (by
    intro a b hab
    exact Quotient.sound (fieldOperator_well_defined Wfn f a b hab))

end Reconstruction

/-! ### The Reconstruction Theorem -/

/-- The Wightman reconstruction theorem (statement).

    Given a collection of Wightman functions W_n satisfying the required properties
    (temperedness, Poincaré covariance, spectral condition, locality, positivity),
    there exists a unique (up to unitary equivalence) Wightman QFT whose n-point
    functions match W_n on product test functions.

    The relationship between the QFT's smeared n-point function and W_n is:
      ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)

    where f₁ ⊗ ··· ⊗ fₙ denotes the tensor product of test functions.

    **Note**: The full proof requires:
    1. GNS construction from the positive definite form on Borchers sequences
    2. Verification that the constructed operators satisfy the Wightman axioms
    3. Nuclear theorem to extend from product to general test functions

    This is a foundational theorem of axiomatic QFT established by Wightman (1956)
    and elaborated in Streater-Wightman (1964). -/
theorem wightman_reconstruction (Wfn : WightmanFunctions d) :
    ∃ (qft : WightmanQFT d),
      -- The reconstructed QFT's n-point functions match W_n on product test functions:
      -- ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)
      ∀ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
        qft.wightmanFunction n fs = Wfn.W n (SchwartzMap.productTensor fs) := by
  -- The construction proceeds via:
  -- 1. Form the pre-Hilbert space of Borchers sequences quotient by null vectors
  -- 2. Complete to obtain the Hilbert space H
  -- 3. Define vacuum Ω as the class of (1, 0, 0, ...)
  -- 4. Define field operators φ(f) via prepending f to sequences
  -- 5. Verify all Wightman axioms (R0-R5)
  -- 6. The key property: ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ = W_n(f₁ ⊗ ··· ⊗ fₙ)
  --    follows from the definition of the inner product and field operator action
  -- See Reconstruction/GNSConstruction.lean for the detailed construction.
  sorry

/-- The uniqueness part: two Wightman QFTs with the same smeared n-point functions
    are unitarily equivalent.

    More precisely, if for all n and all test functions f₁,...,fₙ we have
      ⟨Ω₁, φ₁(f₁)···φ₁(fₙ)Ω₁⟩ = ⟨Ω₂, φ₂(f₁)···φ₂(fₙ)Ω₂⟩
    then there exists a unitary U : H₁ → H₂ such that:
      - U Ω₁ = Ω₂
      - U φ₁(f) U⁻¹ = φ₂(f) for all f -/
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
      qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    ∃ U : qft₁.HilbertSpace →ₗᵢ[ℂ] qft₂.HilbertSpace,
      -- U maps vacuum to vacuum
      U qft₁.vacuum = qft₂.vacuum ∧
      -- U intertwines the field operators: U φ₁(f) = φ₂(f) U on the domain
      (∀ (f : SchwartzSpacetime d) (ψ : qft₁.HilbertSpace),
        ψ ∈ qft₁.field.domain →
        U (qft₁.field.operator f ψ) = qft₂.field.operator f (U ψ)) := by
  sorry

/-! ### Connection to Euclidean Field Theory

The Osterwalder-Schrader (OS) axioms provide an alternative formulation of QFT
in Euclidean signature. The relationship between Wightman and OS axioms is:

**Wightman → OS (Direct, Theorem R→E)**:
Given a Wightman QFT satisfying R0-R5, one obtains Schwinger functions by
Wick rotation (analytic continuation t → -iτ). The Wightman axioms directly
imply the OS axioms E0-E4 for the resulting Euclidean theory.

**OS → Wightman (The OS Gap)**:
The converse is more subtle. In their first paper (OS I, 1973), Osterwalder and
Schrader claimed that axioms E0-E4 were sufficient. However, **Lemma 8.8 of OS I
was found to be incorrect** (first questioned by Simon). In their second paper
(OS II, 1975), they state:

  "At present it is an open question whether the conditions (E0-E4) as introduced
   in OS I are sufficient to guarantee the existence of a Wightman theory."

**The Linear Growth Condition (E0')**:
To fix the reconstruction, OS II introduces the **linear growth condition**:

  (E0') S₀ = 1, Sₙ ∈ S'₀(ℝ^{4n}) and there exist s ∈ ℤ₊ and a sequence {σₙ}
        of factorial growth (σₙ ≤ αβⁿ(n!)^γ for constants α, β, γ), such that
        |Sₙ(f)| ≤ σₙ ‖f‖_{s,n}

The issue is that analytic continuation from Euclidean to Minkowski involves
infinitely many Schwinger functions Sₖ. Without control over the growth of the
order of Sₖ as k → ∞, one cannot prove that the boundary values are tempered
distributions (the Wightman temperedness axiom R0).

**Theorem E'→R' (OS II)**: Schwinger functions satisfying E0' and E1-E4 define
a unique Wightman QFT satisfying R0-R5, with the Wightman distributions also
satisfying a linear growth condition R0'.

References:
- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions" (Commun. Math. Phys. 31, 1973)
- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions II" (Commun. Math. Phys. 42, 1975)
- Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View", Chapter 19
-/

/-- Schwinger functions (Euclidean correlators) -/
def SchwingerFunctions (d : ℕ) := (n : ℕ) → SchwartzNPoint d n → ℂ

/-- The positive Euclidean time region: n-point configurations with all τᵢ > 0. -/
def PositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 > 0 }

/-- Time reflection operator on Euclidean points: θ(τ, x⃗) = (-τ, x⃗) -/
def timeReflection (x : SpacetimeDim d) : SpacetimeDim d :=
  fun i => if i = 0 then -x 0 else x i

/-- Time reflection on n-point configurations -/
def timeReflectionN (x : NPointDomain d n) : NPointDomain d n :=
  fun i => timeReflection d (x i)

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

/-- Time reflection is an involution on Schwartz functions. -/
theorem SchwartzNPoint.timeReflect_timeReflect {n : ℕ} (f : SchwartzNPoint d n) :
    f.timeReflect.timeReflect = f := by
  ext x; simp only [SchwartzNPoint.timeReflect_apply]
  congr 1; funext i; exact timeReflection_timeReflection d (x i)

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

/-- The OS conjugated tensor product: (θf̄) ⊗ g.
    This is the pairing used in the OS inner product for Schwinger functions:
    ⟨F, G⟩_OS = Σ S_{n+m}((θf̄)_n ⊗ g_m)

    Compare with `conjTensorProduct` (Borchers involution) used in
    `WightmanInnerProduct`. -/
def SchwartzNPoint.osConjTensorProduct {m k : ℕ} (f : SchwartzNPoint d m)
    (g : SchwartzNPoint d k) : SchwartzNPoint d (m + k) :=
  f.osConj.tensorProduct g

end TimeReflectSchwartz

/-- The Osterwalder-Schrader inner product on Borchers sequences.

    ⟨F, G⟩_OS = Σ_{n,m} S_{n+m}((θf̄)_n ⊗ g_m)

    where θ is time reflection θ(τ,x⃗) = (-τ,x⃗) and f̄ is complex conjugation.

    This is the correct inner product for the Euclidean (OS) framework.
    Compare with `WightmanInnerProduct` which uses the Borchers involution
    (argument reversal + conjugation) — correct for Wightman functions.

    Reference: Osterwalder-Schrader, Commun. Math. Phys. 31 (1973), §2 -/
def OSInnerProduct (S : SchwingerFunctions d) (F G : BorchersSequence d) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      S (n + m) ((F.funcs n).osConjTensorProduct (G.funcs m))

/-- The Osterwalder-Schrader axioms E0-E4 for Euclidean field theory.

    From OS I (1973):
    - E0: Temperedness (Sₙ ∈ S'(ℝ^{dn}))
    - E1: Euclidean invariance
    - E2: Reflection positivity: Σₙ,ₘ Sₙ₊ₘ(Θf* × fₘ) ≥ 0 for f ∈ S₊
    - E3: Symmetry: Sₙ(f) = Sₙ(f^π) for all permutations π
    - E4: Cluster property

    **Important**: As shown in OS II (1975), these axioms alone may NOT be
    sufficient to reconstruct a Wightman QFT. The linear growth condition E0'
    is needed. See `OSLinearGrowthCondition`. -/
structure OsterwalderSchraderAxioms (d : ℕ) [NeZero d] where
  /-- The Schwinger functions -/
  S : SchwingerFunctions d
  /-- E0: Temperedness - each Sₙ is a tempered distribution (continuous on Schwartz space) -/
  E0_tempered : ∀ n, Continuous (S n)
  /-- E1a: Translation invariance.
      S_n(x₁+a,...,xₙ+a) = S_n(x₁,...,xₙ) for all a ∈ ℝ^{d+1}. -/
  E1_translation_invariant : ∀ (n : ℕ) (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
    (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
    S n f = S n g
  /-- E1b: Rotation invariance under SO(d+1).
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(d+1).
      Together with E1a, this gives Euclidean covariance under ℝ^{d+1} ⋊ SO(d+1).
      Note: Full O(d+1) invariance (including improper rotations with det=-1)
      would require parity invariance, which is not implied by the Wightman axioms. -/
  E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    R.transpose * R = 1 → R.det = 1 →
    ∀ (f g : SchwartzNPoint d n),
    (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
    S n f = S n g
  /-- E2: Reflection positivity - the crucial axiom for Hilbert space construction.
      For test functions F supported in the positive time half-space (τ > 0),
      Σₙ,ₘ S_{n+m}(θf̄ₙ ⊗ fₘ) ≥ 0
      where θ is time reflection θ(τ,x⃗) = (-τ,x⃗) and f̄ is complex conjugation.
      This uses `OSInnerProduct` (time reflection + conjugation), the correct
      inner product for the Euclidean framework.
      This ensures the reconstructed inner product is positive definite. -/
  E2_reflection_positive : ∀ (F : BorchersSequence d),
    (∀ n, ∀ x : NPointDomain d n, (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion d n) →
    (OSInnerProduct d S F F).re ≥ 0
  /-- E3: Permutation symmetry - Schwinger functions are symmetric under
      permutation of arguments: S_n(x_{σ(1)},...,x_{σ(n)}) = S_n(x₁,...,xₙ)
      for all permutations σ ∈ Sₙ. -/
  E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n),
    (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
    S n f = S n g
  /-- E4: Cluster property - factorization at large separations.
      lim_{|a|→∞} S_{n+m}(x₁,...,xₙ,y₁+a,...,yₘ+a) = S_n(x₁,...,xₙ) · S_m(y₁,...,yₘ)
      This reflects the uniqueness of the vacuum in the reconstructed theory.

      Expressed via the connected n-point functions: the connected part Sₙᶜ vanishes
      for n ≥ 2 at large separations. Equivalently, for product test functions
      with widely separated supports, S_{n+m} factorizes. -/
  E4_cluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
    -- Cluster property: as spatial separation increases, S_{n+m} factorizes.
    -- For any ε > 0, there exists R > 0 such that for spatial translation a with |a| > R,
    -- |S_{n+m}(f ⊗ τ_a g) - S_n(f) · S_m(g)| < ε
    -- where τ_a g is g translated by a in all m coordinates.
    -- The translation a must be purely spatial (a 0 = 0): Euclidean time shifts
    -- correspond to imaginary Minkowski time, leaving the cluster property's domain.
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        -- For any Schwartz function g_a that is the translation of g by a:
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖S (n + m) (f.tensorProduct g_a) - S n f * S m g‖ < ε

/-- The linear growth condition E0' from OS II (1975).

    This replaces the simple temperedness E0 with a stronger condition:
    There exist s ∈ ℤ₊ and constants α, β, γ such that for σₙ ≤ αβⁿ(n!)^γ,
      |Sₙ(f)| ≤ σₙ ‖f‖_{s,n}

    This condition controls the growth of the distribution order as n → ∞,
    which is essential for proving temperedness of the reconstructed
    Wightman distributions. -/
structure OSLinearGrowthCondition (d : ℕ) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  /-- The Sobolev index s -/
  sobolev_index : ℕ
  /-- Factorial growth bound constants: σₙ ≤ α · βⁿ · (n!)^γ -/
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  /-- The bounds are positive -/
  alpha_pos : alpha > 0
  beta_pos : beta > 0
  /-- The linear growth estimate: |Sₙ(f)| ≤ σₙ · ‖f‖_{s,n}
      where σₙ ≤ α · βⁿ · (n!)^γ bounds the distribution order growth,
      and ‖f‖_{s,n} is the Schwartz seminorm of order s on n-point functions.

      This is equation (4.1) of OS II: |Sₙ(f)| ≤ σₙ |f|_s
      where |f|_s = SchwartzMap.seminorm ℝ s s (f). -/
  growth_estimate : ∀ (n : ℕ) (f : SchwartzNPoint d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      SchwartzMap.seminorm ℝ sobolev_index sobolev_index f

/-- The relationship between Wightman and Schwinger functions:
    the two sets of correlation functions are analytic continuations of each other.

    Formally: there exists a holomorphic function on the forward tube
    (the "analytic continuation") that:
    1. Has distributional boundary values equal to the Wightman functions W_n
    2. When restricted to Euclidean points (via Wick rotation) and paired with
       test functions, reproduces the Schwinger functions S_n

    This is the mathematical content of the Wick rotation.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def IsWickRotationPair {d : ℕ} [NeZero d] (S : SchwingerFunctions d) (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ (n : ℕ), ∃ (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
    -- F_analytic is holomorphic on the forward tube
    DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
    -- Boundary values of F_analytic = W_n (as distributions):
    -- For each test function f and approach direction η ∈ V₊,
    -- lim_{ε→0⁺} ∫ F_analytic(x + iεη) f(x) dx = W_n(f)
    (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      (∀ k, InOpenForwardCone d (η k)) →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f))) ∧
    -- Euclidean restriction gives S_n: integrating F_analytic ∘ Wick against f gives S_n(f)
    (∀ (f : SchwartzNPoint d n),
      S n f = ∫ x : NPointDomain d n,
        F_analytic (fun k => wickRotatePoint (x k)) * (f x))

/-- Theorem R→E (Wightman → OS): A Wightman QFT yields Schwinger functions
    satisfying OS axioms E0-E4.

    The Schwinger functions are related to the Wightman functions by Wick rotation
    (analytic continuation): the Schwinger functions are Euclidean restrictions of the
    analytic continuation whose boundary values are the Wightman functions.

    The construction (OS I, Section 5) uses the Bargmann-Hall-Wightman theorem:
    - The spectrum condition R3 implies W_n is analytic in the forward tube T_n
    - BHW extends W_n to the permuted extended tube (invariant under complex Lorentz)
    - Define S_n by restricting W_n to Euclidean points: S_n(x) = W_n(ix⁰₁, x⃗₁, ...)
    - Euclidean points lie inside the permuted extended tube, so S_n is real-analytic

    Key subtlety: In the forward tube, Im(z_k - z_{k-1}) ∈ V₊ forces time ordering.
    But the permuted extended tube covers all orderings, yielding full permutation
    symmetry (E3). Euclidean invariance (E1) follows from complex Lorentz invariance
    of W_n: SO(d+1) ⊂ L₊(ℂ) is the subgroup preserving Euclidean points.

    Temperedness (E0) requires Proposition 5.1 of OS I (a geometric lemma on Ω_n).
    Reflection positivity (E2) follows from Wightman positivity (R2).
    Cluster (E4) follows from R4. -/
theorem wightman_to_os (Wfn : WightmanFunctions d) :
    ∃ (OS : OsterwalderSchraderAxioms d),
      IsWickRotationPair OS.S Wfn.W := by
  -- See Reconstruction/WickRotation.lean for the detailed proof (wightman_to_os_full).
  sorry

/-- Theorem E'→R' (OS II): Schwinger functions satisfying the linear growth
    condition E0' together with E1-E4 can be analytically continued to
    Wightman distributions satisfying R0-R5.

    The Wightman functions are the boundary values of the analytic continuation
    of the Schwinger functions to the forward tube.

    **Critical**: Without the linear growth condition, this theorem may be FALSE.
    The issue is that analytic continuation involves infinitely many Sₖ, and
    without growth control, the boundary values may fail to be tempered.

    The reconstructed Wightman distributions also satisfy a linear growth
    condition R0'. -/
theorem os_to_wightman (OS : OsterwalderSchraderAxioms d)
    (linear_growth : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.S Wfn.W := by
  -- See Reconstruction/WickRotation.lean for the detailed proof (os_to_wightman_full).
  sorry

end

