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

@[simp] theorem linearCombo_empty {ι : Type*} [DecidableEq ι]
    (c : ι → ℂ) (G : ι → BorchersSequence d) (n : ℕ) :
    (linearCombo ∅ c G).funcs n = (0 : BorchersSequence d).funcs n := by
  simp [linearCombo]

@[simp] theorem linearCombo_funcs {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (G : ι → BorchersSequence d) (n : ℕ) :
    (linearCombo s c G).funcs n = ∑ i ∈ s, c i • (G i).funcs n := rfl

theorem linearCombo_insert {ι : Type*} [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s)
    (c : ι → ℂ) (G : ι → BorchersSequence d) (n : ℕ) :
    (linearCombo (insert a s) c G).funcs n =
      (c a • G a + linearCombo s c G).funcs n := by
  simp [linearCombo_funcs, Finset.sum_insert ha, add_funcs, smul_funcs]

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
      -- For any test function f and approach direction η ∈ ForwardConeAbs,
      -- lim_{ε→0⁺} ∫ W_analytic(x + iε·η) f(x) dx = W_n(f)
      -- This is the distributional boundary value condition:
      -- the smeared analytic continuation converges to the Wightman distribution.
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
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
  /-- Cluster decomposition (R4): as the spacelike separation between two groups of
      arguments grows, the Wightman function factorizes.

      For any n, m, test functions f, g, and ε > 0, there exists R > 0 such that for
      any purely spatial translation a with |a| > R:
        |W_{n+m}(f ⊗ τ_a g) - W_n(f) · W_m(g)| < ε

      This axiom is equivalent to uniqueness of the vacuum in the reconstructed
      Hilbert space: the only translation-invariant vector is the vacuum.

      Ref: Streater-Wightman, Theorem 3-5; Glimm-Jaffe, Theorem 19.4.1 -/
  cluster : ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ (g_a : SchwartzNPoint d m),
          (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
          ‖W (n + m) (f.tensorProduct g_a) - W n f * W m g‖ < ε

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

/-- Linearity in test function (addition): φ(f+g)F has same funcs as φ(f)F + φ(g)F. -/
theorem fieldOperatorAction_add_test_funcs (f g : SchwartzSpacetime d)
    (F : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction (f + g) F).funcs n =
    (fieldOperatorAction f F + fieldOperatorAction g F).funcs n := by
  cases n with
  | zero => simp
  | succ k => simp [SchwartzMap.prependField_add_left, BorchersSequence.add_funcs]

/-- Scalar linearity in test function: φ(c·f)F has same funcs as c·(φ(f)F). -/
theorem fieldOperatorAction_smul_test_funcs (c : ℂ) (f : SchwartzSpacetime d)
    (F : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction (c • f) F).funcs n =
    (c • fieldOperatorAction f F).funcs n := by
  cases n with
  | zero => simp
  | succ k => simp [SchwartzMap.prependField_smul_left, BorchersSequence.smul_funcs]

/-- Linearity in vector (addition): φ(f)(F+G) has same funcs as φ(f)F + φ(f)G. -/
theorem fieldOperatorAction_add_vec_funcs (f : SchwartzSpacetime d)
    (F G : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction f (F + G)).funcs n =
    (fieldOperatorAction f F + fieldOperatorAction f G).funcs n := by
  cases n with
  | zero => simp
  | succ k => simp [SchwartzMap.prependField_add_right, BorchersSequence.add_funcs]

/-- Scalar linearity in vector: φ(f)(c·F) has same funcs as c·(φ(f)F). -/
theorem fieldOperatorAction_smul_vec_funcs (f : SchwartzSpacetime d)
    (c : ℂ) (F : BorchersSequence d) (n : ℕ) :
    (fieldOperatorAction f (c • F)).funcs n =
    (c • fieldOperatorAction f F).funcs n := by
  cases n with
  | zero => simp
  | succ k => simp [SchwartzMap.prependField_smul_right, BorchersSequence.smul_funcs]

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

-- `wightman_reconstruction` and `wightman_uniqueness` moved to Reconstruction/Main.lean
-- (proved via GNS construction in GNSHilbertSpace.lean)

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

/-- The positive Euclidean time region: n-point configurations with all τᵢ > 0. -/
def PositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 > 0 }

/-- The OS-I ordered positive-time region: `0 < x₁⁰ < ... < xₙ⁰`.

    This is the support surface used in the positivity axiom `E2`, matching the
    test-function space `S^<_{+}` in OS I. -/
def OrderedPositiveTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, 0 < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0 }

/-- The time-reflected ordered region: all times are negative and strictly decrease. -/
def OrderedNegativeTimeRegion (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∀ i : Fin n, x i 0 < 0 ∧ ∀ j : Fin n, i < j → x j 0 < x i 0 }

theorem OrderedPositiveTimeRegion_subset_positiveTimeRegion (d n : ℕ) :
    OrderedPositiveTimeRegion d n ⊆ PositiveTimeRegion d n := by
  intro x hx i
  exact (hx i).1

/-- The coincidence locus where at least two Euclidean arguments coincide. -/
def CoincidenceLocus (d n : ℕ) : Set (NPointDomain d n) :=
  { x | ∃ i j : Fin n, i ≠ j ∧ x i = x j }

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
private theorem continuous_coincidenceCollapse {n : ℕ} (i j : Fin n) :
    Continuous (coincidenceCollapse (d := d) i j) := by
  apply continuous_pi
  intro k
  by_cases hk : k = i ∨ k = j
  · simpa [coincidenceCollapse, hk, midpoint_eq_smul_add] using
      (((continuous_apply i : Continuous fun x : NPointDomain d n => x i)).add
        (continuous_apply j : Continuous fun x : NPointDomain d n => x j)).const_smul
        (⅟ (2 : ℝ))
  · simpa [coincidenceCollapse, hk] using
      (continuous_apply k : Continuous fun x : NPointDomain d n => x k)

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

/-- On compact sets, a test function vanishing on the coincidence locus is
    Lipschitz in each coincidence direction.

    More precisely: fixing a pair of indices `i ≠ j`, the value of `f(x)` is
    controlled by the separation `‖x i - x j‖` on any compact set. This is the
    first quantitative consequence of the zero-diagonal condition and is the
    order-1 prototype for the higher-power distance estimates still needed in
    the Euclidean E0 integrability theorem. -/
theorem VanishesToInfiniteOrderOnCoincidence.norm_le_pairDifference_on_isCompact
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖f x‖ ≤ C * ‖x i - x j‖ := by
  let c : NPointDomain d n → NPointDomain d n := coincidenceCollapse (d := d) i j
  have hc_cont : Continuous c := continuous_coincidenceCollapse (d := d) i j
  let Φ : NPointDomain d n × ℝ → NPointDomain d n :=
    fun p => c p.1 + p.2 • (p.1 - c p.1)
  have hΦ_cont : Continuous Φ := by
    exact (hc_cont.comp continuous_fst).add <|
      continuous_snd.smul <|
        continuous_fst.sub (hc_cont.comp continuous_fst)
  have hSegCompact :
      IsCompact (Φ '' (K ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (hK.prod isCompact_Icc).image hΦ_cont
  have hfd_cont :
      Continuous fun x : NPointDomain d n => ‖fderiv ℝ (f : NPointDomain d n → ℂ) x‖ := by
    exact (((f : SchwartzNPoint d n).smooth 1).continuous_fderiv one_ne_zero).norm
  obtain ⟨C, hC⟩ :=
    hSegCompact.exists_bound_of_continuousOn
      (f := fun x : NPointDomain d n => ‖fderiv ℝ (f : NPointDomain d n → ℂ) x‖)
      hfd_cont.continuousOn
  let C' : ℝ := max C 0
  refine ⟨C', le_max_right _ _, ?_⟩
  intro x hx
  have hx_seg :
      segment ℝ (c x) x ⊆ Φ '' (K ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
    simp [Φ, AffineMap.lineMap_apply_module', add_comm]
  have hbound_seg :
      ∀ z ∈ segment ℝ (c x) x,
        ‖fderiv ℝ (f : NPointDomain d n → ℂ) z‖ ≤ C' := by
    intro z hz
    have hz' : z ∈ Φ '' (K ×ˢ Set.Icc (0 : ℝ) 1) := hx_seg hz
    have hzC : ‖fderiv ℝ (f : NPointDomain d n → ℂ) z‖ ≤ C := by
      simpa using hC z hz'
    exact hzC.trans (le_max_left _ _)
  have hc_coin : c x ∈ CoincidenceLocus d n := by
    simpa [c] using coincidenceCollapse_mem_CoincidenceLocus (d := d) x i j hij
  have hc_zero : f (c x) = 0 := by
    apply norm_eq_zero.mp
    simpa [norm_iteratedFDeriv_zero] using
      congrArg norm (hf 0 (c x) hc_coin)
  have hmv :
      ‖f x - f (c x)‖ ≤ C' * ‖x - c x‖ := by
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := segment ℝ (c x) x)
      (f := (f : NPointDomain d n → ℂ))
      (x := c x) (y := x)
      (hf := fun z _ => (f : SchwartzNPoint d n).differentiableAt)
      hbound_seg
      (convex_segment (c x) x)
      (left_mem_segment ℝ (c x) x) (right_mem_segment ℝ (c x) x)
  have hdist :
      ‖x - c x‖ ≤ ‖x i - x j‖ := by
    simpa [c] using norm_sub_coincidenceCollapse_le_pairDifference (d := d) x i j hij
  calc
    ‖f x‖ = ‖f x - f (c x)‖ := by simp [hc_zero]
    _ ≤ C' * ‖x - c x‖ := hmv
    _ ≤ C' * ‖x i - x j‖ := by gcongr

/-- On compact sets, a test function vanishing to infinite order on the
    coincidence locus vanishes to arbitrarily high finite order in each fixed
    coincidence direction. -/
theorem VanishesToInfiniteOrderOnCoincidence.norm_le_pairDifference_pow_succ_on_isCompact
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (m : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖f x‖ ≤ C * ‖x i - x j‖ ^ (m + 1) := by
  let c : NPointDomain d n → NPointDomain d n := coincidenceCollapse (d := d) i j
  have hc_cont : Continuous c := continuous_coincidenceCollapse (d := d) i j
  let Φ : NPointDomain d n × ℝ → NPointDomain d n :=
    fun p => c p.1 + p.2 • (p.1 - c p.1)
  have hΦ_cont : Continuous Φ := by
    exact (hc_cont.comp continuous_fst).add <|
      continuous_snd.smul <|
        continuous_fst.sub (hc_cont.comp continuous_fst)
  have hSegCompact :
      IsCompact (Φ '' (K ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (hK.prod isCompact_Icc).image hΦ_cont
  have hfd_cont :
      Continuous fun x : NPointDomain d n =>
        iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) x := by
    exact ((f : SchwartzNPoint d n).smooth (m + 1)).continuous_iteratedFDeriv'
  obtain ⟨A, hA⟩ :=
    hSegCompact.exists_bound_of_continuousOn
      (f := fun x : NPointDomain d n =>
        iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) x)
      hfd_cont.continuousOn
  let A' : ℝ := max A 0
  refine ⟨A' / ((Nat.factorial m : ℕ) : ℝ), div_nonneg (le_max_right _ _) (by positivity), ?_⟩
  intro x hx
  let v : NPointDomain d n := x - c x
  let L : ℝ →L[ℝ] NPointDomain d n :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let g : ℝ → ℂ :=
    (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c x)) ∘ L
  have hshift_contDiff :
      ∀ r : ℕ, ContDiff ℝ r (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c x)) :=
    fun r => by
      simpa using ((f : SchwartzNPoint d n).smooth r).comp (contDiff_id.add contDiff_const)
  have hg_contDiff : ∀ r : ℕ, ContDiff ℝ r g := fun r => by
    simpa [g] using (ContDiff.comp_continuousLinearMap (g := L) (hf := hshift_contDiff r))
  have hc_coin : c x ∈ CoincidenceLocus d n := by
    simpa [c] using coincidenceCollapse_mem_CoincidenceLocus (d := d) x i j hij
  have hTaylor_zero :
      taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hk_mem : k ∈ Finset.range (m + 1) := hk
    have hk_lt : k < m + 1 := Finset.mem_range.mp hk_mem
    have hk_zero :
        iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
        ((hg_contDiff k).contDiffAt) (by simp), iteratedDeriv_eq_iteratedFDeriv]
      have hcomp :
          iteratedFDeriv ℝ k g 0 =
            (iteratedFDeriv ℝ k (fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c x))
              (L 0)).compContinuousLinearMap fun _ : Fin k => L := by
        simpa [g] using
          L.iteratedFDeriv_comp_right
            (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c x))
            (hshift_contDiff k) (x := 0) (i := k) le_rfl
      have hzeroF :
          iteratedFDeriv ℝ k (f : NPointDomain d n → ℂ) (L 0 + c x) = 0 := by
        simpa [L, ContinuousLinearMap.smulRight_apply] using hf k (c x) hc_coin
      rw [hcomp, iteratedFDeriv_comp_add_right, hzeroF]
      simp
    simp [hk_zero]
  have hderiv_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin (m + 1) g (Set.Icc (0 : ℝ) 1) t‖ ≤
          A' * ‖v‖ ^ (m + 1) := by
    intro t ht
    have ht_seg : c x + t • v ∈ Φ '' (K ×ˢ Set.Icc (0 : ℝ) 1) := by
      refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
      simp [Φ, c, v]
    have hA' :
        ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (c x + t • v)‖ ≤ A' := by
      exact (hA _ ht_seg).trans (le_max_left _ _)
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
            (z + c x)) (L t)).compContinuousLinearMap fun _ : Fin (m + 1) => L := by
      simpa [g] using
        L.iteratedFDeriv_comp_right
          (f := fun z : NPointDomain d n => (f : NPointDomain d n → ℂ) (z + c x))
          (hshift_contDiff (m + 1)) (x := t) (i := m + 1) le_rfl
    rw [hcomp, iteratedFDeriv_comp_add_right]
    calc
      ‖(iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c x)).compContinuousLinearMap
          (fun _ : Fin (m + 1) => L)‖ ≤
          ‖iteratedFDeriv ℝ (m + 1) (f : NPointDomain d n → ℂ) (L t + c x)‖ *
            ∏ _ : Fin (m + 1), ‖L‖ := by
              exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ A' * ∏ _ : Fin (m + 1), ‖L‖ := by
          gcongr
          simpa [L, v, ContinuousLinearMap.smulRight_apply, add_comm] using hA'
      _ = A' * ‖L‖ ^ (m + 1) := by simp
      _ ≤ A' * ‖v‖ ^ (m + 1) := by
          gcongr
  have hrem :=
    taylor_mean_remainder_bound (f := g) (a := (0 : ℝ)) (b := 1)
      (C := A' * ‖v‖ ^ (m + 1)) (x := 1) (n := m) (by norm_num)
      (hg_contDiff (m + 1)).contDiffOn (by simp) hderiv_bound
  have hdist :
      ‖v‖ ≤ ‖x i - x j‖ := by
    simpa [v, c] using norm_sub_coincidenceCollapse_le_pairDifference (d := d) x i j hij
  have hg_one : g 1 = f x := by
    simp [g, L, v, ContinuousLinearMap.smulRight_apply]
  calc
    ‖f x‖ = ‖g 1 - taylorWithinEval g m (Set.Icc (0 : ℝ) 1) 0 1‖ := by
      rw [hg_one]
      simp [hTaylor_zero]
    _ ≤ A' * ‖v‖ ^ (m + 1) * (1 - (0 : ℝ)) ^ (m + 1) / (((Nat.factorial m : ℕ) : ℝ)) := by
      simpa [hTaylor_zero] using hrem
    _ = (A' / (((Nat.factorial m : ℕ) : ℝ))) * ‖v‖ ^ (m + 1) := by
      field_simp [Nat.cast_ne_zero]
      ring
    _ ≤ (A' / (((Nat.factorial m : ℕ) : ℝ))) * ‖x i - x j‖ ^ (m + 1) := by
      gcongr

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

/-- Higher-order compact flatness in terms of actual distance to the coincidence
    locus. This is the `N = m + 1` upgrade of the first-order `infDist` bound. -/
theorem VanishesToInfiniteOrderOnCoincidence.norm_le_infDist_CoincidenceLocus_pow_succ_on_isCompact
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (m : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖f x‖ ≤ C * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
  classical
  let P : Type := {p : Fin n × Fin n // p.1 ≠ p.2}
  have hP_nonempty : Nonempty P := by
    rcases hcoin with ⟨x, hx⟩
    rcases hx with ⟨i, j, hij, _⟩
    exact ⟨⟨(i, j), hij⟩⟩
  have hpair :
      ∀ p : P, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ K, ‖f x‖ ≤ C * ‖x p.1.1 - x p.1.2‖ ^ (m + 1) := by
    intro p
    exact
      VanishesToInfiniteOrderOnCoincidence.norm_le_pairDifference_pow_succ_on_isCompact
        hf hK m p.1.1 p.1.2 p.2
  choose C hC_nonneg hC_bound using hpair
  let Cmax : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hC_le : ∀ p : P, C p ≤ Cmax := by
    intro p
    exact Finset.le_sup' (f := C) (Finset.mem_univ p)
  let p0 : P := Classical.choice hP_nonempty
  have hCmax_nonneg : 0 ≤ Cmax := le_trans (hC_nonneg p0) (hC_le p0)
  refine ⟨Cmax * (2 : ℝ) ^ (m + 1), mul_nonneg hCmax_nonneg (pow_nonneg (by norm_num) _), ?_⟩
  intro x hx
  obtain ⟨i, j, hij, hijdist⟩ :=
    exists_pairDifference_le_two_infDist_CoincidenceLocus (d := d) (n := n) x hcoin
  let p : P := ⟨(i, j), hij⟩
  calc
    ‖f x‖ ≤ C p * ‖x i - x j‖ ^ (m + 1) := hC_bound p x hx
    _ ≤ Cmax * ‖x i - x j‖ ^ (m + 1) := by
        exact mul_le_mul_of_nonneg_right (hC_le p) (pow_nonneg (norm_nonneg _) _)
    _ ≤ Cmax * (2 * Metric.infDist x (CoincidenceLocus d n)) ^ (m + 1) := by
        gcongr
    _ = (Cmax * (2 : ℝ) ^ (m + 1)) * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) := by
        rw [mul_pow]
        ring

/-- First-order compact flatness in terms of actual distance to the coincidence
    locus. This packages the pairwise mean-value estimate using a nearest
    coincidence point and a finite maximum over all pairs. -/
theorem VanishesToInfiniteOrderOnCoincidence.norm_le_infDist_CoincidenceLocus_on_isCompact
    {d n : ℕ} {f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hcoin : (CoincidenceLocus d n).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ‖f x‖ ≤ C * Metric.infDist x (CoincidenceLocus d n) := by
  classical
  let P : Type := {p : Fin n × Fin n // p.1 ≠ p.2}
  have hP_nonempty : Nonempty P := by
    rcases hcoin with ⟨x, hx⟩
    rcases hx with ⟨i, j, hij, _⟩
    exact ⟨⟨(i, j), hij⟩⟩
  have hpair :
      ∀ p : P, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ K, ‖f x‖ ≤ C * ‖x p.1.1 - x p.1.2‖ := by
    intro p
    exact VanishesToInfiniteOrderOnCoincidence.norm_le_pairDifference_on_isCompact
      hf hK p.1.1 p.1.2 p.2
  choose C hC_nonneg hC_bound using hpair
  let Cmax : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hC_le : ∀ p : P, C p ≤ Cmax := by
    intro p
    exact Finset.le_sup' (f := C) (Finset.mem_univ p)
  let p0 : P := Classical.choice hP_nonempty
  have hCmax_nonneg : 0 ≤ Cmax := le_trans (hC_nonneg p0) (hC_le p0)
  refine ⟨2 * Cmax, mul_nonneg (by norm_num) hCmax_nonneg, ?_⟩
  intro x hx
  obtain ⟨i, j, hij, hijdist⟩ :=
    exists_pairDifference_le_two_infDist_CoincidenceLocus (d := d) (n := n) x hcoin
  let p : P := ⟨(i, j), hij⟩
  calc
    ‖f x‖ ≤ C p * ‖x i - x j‖ := hC_bound p x hx
    _ ≤ Cmax * ‖x i - x j‖ := by
      exact mul_le_mul_of_nonneg_right (hC_le p) (norm_nonneg _)
    _ ≤ Cmax * (2 * Metric.infDist x (CoincidenceLocus d n)) := by
      gcongr
    _ = (2 * Cmax) * Metric.infDist x (CoincidenceLocus d n) := by ring

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
private abbrev reindexSchwartz {k l : ℕ} (σ : Fin k ≃ Fin l) (f : SchwartzNPoint d k) :
    SchwartzNPoint d l :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) σ).toContinuousLinearEquiv) f

omit [NeZero d] in
@[simp] private theorem reindexSchwartz_apply {k l : ℕ} (σ : Fin k ≃ Fin l)
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

/-- Time reflection is an involution on Schwartz functions. -/
theorem SchwartzNPoint.timeReflect_timeReflect {n : ℕ} (f : SchwartzNPoint d n) :
    f.timeReflect.timeReflect = f := by
  ext x; simp only [SchwartzNPoint.timeReflect_apply]
  congr 1; funext i; exact timeReflection_timeReflection d (x i)

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
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

/-! ### OS Inner Product Algebra

The standard OS semigroup/spectral argument needs sesquilinearity of the
reflection-positive form. Since `S n` is part of E0 and therefore a tempered
distribution, the required linearity is part of the correct interface. The
lemmas below mirror the existing `WightmanInnerProduct` algebra.

Because `OSInnerProduct` is totalized via `ZeroDiagonalSchwartz.ofClassical`,
additivity theorems must explicitly assume that the relevant OS tensor terms
really lie in `°S`; otherwise the fallback zero branch can destroy algebraic
identities. -/

/-- The OS inner product with explicit summation bounds. -/
def OSInnerProductN (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (F G : BorchersSequence d) (N₁ N₂ : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N₁,
    ∑ m ∈ Finset.range N₂,
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

/-- The standard OS inner product equals the naturally bounded version. -/
theorem OSInnerProduct_eq_N (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (F G : BorchersSequence d) :
    OSInnerProduct d S F G = OSInnerProductN d S F G (F.bound + 1) (G.bound + 1) :=
  rfl

/-- The genuine zero-diagonal compatibility condition for the OS tensor terms
    appearing in `OSInnerProduct`.

    This is the precise hypothesis needed for additive manipulations on the
    Euclidean side after the hard cut to `ZeroDiagonalSchwartz`. -/
def OSTensorAdmissible (F G : BorchersSequence d) : Prop :=
  ∀ n m, VanishesToInfiniteOrderOnCoincidence
    ((F.funcs n).osConjTensorProduct (G.funcs m))

@[simp]
theorem SchwartzNPoint.osConj_zero {n : ℕ} :
    (0 : SchwartzNPoint d n).osConj = 0 := by
  ext x
  simp [SchwartzNPoint.osConj]

theorem SchwartzNPoint.osConj_add {n : ℕ} (f g : SchwartzNPoint d n) :
    (f + g).osConj = f.osConj + g.osConj := by
  ext x
  simp [SchwartzNPoint.osConj]

theorem SchwartzNPoint.osConj_smul {n : ℕ} (c : ℂ) (f : SchwartzNPoint d n) :
    (c • f).osConj = starRingEnd ℂ c • f.osConj := by
  ext x
  simp [SchwartzNPoint.osConj, smul_eq_mul]

@[simp]
theorem SchwartzNPoint.osConjTensorProduct_zero_left {m k : ℕ}
    (g : SchwartzNPoint d k) :
    (0 : SchwartzNPoint d m).osConjTensorProduct g = 0 := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_zero,
    SchwartzMap.tensorProduct_zero_left]

@[simp]
theorem SchwartzNPoint.osConjTensorProduct_zero_right {m k : ℕ}
    (f : SchwartzNPoint d m) :
    f.osConjTensorProduct (0 : SchwartzNPoint d k) = 0 := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_zero_right]

theorem SchwartzNPoint.osConjTensorProduct_add_right {m k : ℕ}
    (f : SchwartzNPoint d m) (g₁ g₂ : SchwartzNPoint d k) :
    f.osConjTensorProduct (g₁ + g₂) =
      f.osConjTensorProduct g₁ + f.osConjTensorProduct g₂ := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_add_right]

theorem SchwartzNPoint.osConjTensorProduct_add_left {m k : ℕ}
    (f₁ f₂ : SchwartzNPoint d m) (g : SchwartzNPoint d k) :
    (f₁ + f₂).osConjTensorProduct g =
      f₁.osConjTensorProduct g + f₂.osConjTensorProduct g := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_add,
    SchwartzMap.tensorProduct_add_left]

theorem SchwartzNPoint.osConjTensorProduct_smul_right {m k : ℕ}
    (f : SchwartzNPoint d m) (c : ℂ) (g : SchwartzNPoint d k) :
    f.osConjTensorProduct (c • g) = c • (f.osConjTensorProduct g) := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_smul_right]

theorem SchwartzNPoint.osConjTensorProduct_smul_left {m k : ℕ}
    (c : ℂ) (f : SchwartzNPoint d m) (g : SchwartzNPoint d k) :
    (c • f).osConjTensorProduct g = starRingEnd ℂ c • (f.osConjTensorProduct g) := by
  simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_smul,
    SchwartzMap.tensorProduct_smul_left]

theorem OSTensorAdmissible.zero_right (F : BorchersSequence d) :
    OSTensorAdmissible d F 0 := by
  intro n m
  simpa [BorchersSequence.zero_funcs] using
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))

theorem OSTensorAdmissible.zero_left (G : BorchersSequence d) :
    OSTensorAdmissible d (0 : BorchersSequence d) G := by
  intro n m
  simpa [BorchersSequence.zero_funcs] using
    (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))

theorem OSTensorAdmissible.add_right {F G₁ G₂ : BorchersSequence d}
    (hFG₁ : OSTensorAdmissible d F G₁)
    (hFG₂ : OSTensorAdmissible d F G₂) :
    OSTensorAdmissible d F (G₁ + G₂) := by
  intro n m
  simpa [BorchersSequence.add_funcs, SchwartzNPoint.osConjTensorProduct_add_right] using
    (hFG₁ n m).add (hFG₂ n m)

theorem OSTensorAdmissible.add_left {F₁ F₂ G : BorchersSequence d}
    (hF₁G : OSTensorAdmissible d F₁ G)
    (hF₂G : OSTensorAdmissible d F₂ G) :
    OSTensorAdmissible d (F₁ + F₂) G := by
  intro n m
  simpa [BorchersSequence.add_funcs, SchwartzNPoint.osConjTensorProduct_add_left] using
    (hF₁G n m).add (hF₂G n m)

theorem OSTensorAdmissible.smul_right {F G : BorchersSequence d}
    (hFG : OSTensorAdmissible d F G) (c : ℂ) :
    OSTensorAdmissible d F (c • G) := by
  intro n m
  simpa [BorchersSequence.smul_funcs, SchwartzNPoint.osConjTensorProduct_smul_right] using
    (hFG n m).smul c

theorem OSTensorAdmissible.smul_left {F G : BorchersSequence d}
    (hFG : OSTensorAdmissible d F G) (c : ℂ) :
    OSTensorAdmissible d (c • F) G := by
  intro n m
  simpa [BorchersSequence.smul_funcs, SchwartzNPoint.osConjTensorProduct_smul_left] using
    (hFG n m).smul (starRingEnd ℂ c)

/-- Ordered positive-time topological support is enough to guarantee that every
    OS tensor term of two Borchers sequences already lies in `°S`. -/
theorem OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
    (F G : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hG : ∀ n, tsupport ((G.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    OSTensorAdmissible d F G := by
  intro n m
  exact VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d) (f := F.funcs n) (g := G.funcs m) (hF n) (hG m)

/-- The honest Euclidean Borchers algebra for OS reflection positivity:
    finitely supported sequences whose every component is topologically supported
    in the ordered positive-time region. On this subtype the OS tensor terms are
    automatically admissible. -/
structure PositiveTimeBorchersSequence (d : ℕ) where
  toBorchersSequence : BorchersSequence d
  ordered_tsupport : ∀ n,
    tsupport ((toBorchersSequence.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n

namespace PositiveTimeBorchersSequence

variable {d : ℕ}

/-- The positive-time Borchers sequence concentrated in degree `n` with component `f`. -/
def single (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence := BorchersSequence.single n f
  ordered_tsupport m := by
    by_cases h : m = n
    · subst h
      simpa using hf
    · have hzero :
        (((BorchersSequence.single n f).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ) = 0 := by
        simp [BorchersSequence.single, h]
      rw [hzero]
      simpa using (empty_subset (OrderedPositiveTimeRegion d m) :
        (∅ : Set (NPointDomain d m)) ⊆ OrderedPositiveTimeRegion d m)

instance : Coe (PositiveTimeBorchersSequence d) (BorchersSequence d) :=
  ⟨PositiveTimeBorchersSequence.toBorchersSequence⟩

instance : Zero (PositiveTimeBorchersSequence d) where
  zero :=
    ⟨0, fun n => by
      simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
        (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)⟩

instance : Add (PositiveTimeBorchersSequence d) where
  add F G :=
    ⟨(F : BorchersSequence d) + (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) +
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.add_funcs] using hx
      have hx'' := (tsupport_add
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.ordered_tsupport n hxF)
        (fun hxG => G.ordered_tsupport n hxG)⟩

instance : Neg (PositiveTimeBorchersSequence d) where
  neg F := ⟨-(F : BorchersSequence d), fun n => by
    rw [show (((-(F : BorchersSequence d)).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) = -(((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) by rfl]
    rw [tsupport_neg]
    exact F.ordered_tsupport n⟩

instance : SMul ℂ (PositiveTimeBorchersSequence d) where
  smul c F :=
    ⟨c • (F : BorchersSequence d), fun n =>
      (tsupport_smul_subset_right
        (fun _ : NPointDomain d n => c)
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))).trans (F.ordered_tsupport n)⟩

instance : Sub (PositiveTimeBorchersSequence d) where
  sub F G :=
    ⟨(F : BorchersSequence d) - (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) -
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.sub_funcs] using hx
      have hx'' := (tsupport_sub
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.ordered_tsupport n hxF)
        (fun hxG => G.ordered_tsupport n hxG)⟩

@[simp] theorem zero_toBorchersSequence :
    ((0 : PositiveTimeBorchersSequence d) : BorchersSequence d) = 0 := rfl

@[simp] theorem add_toBorchersSequence (F G : PositiveTimeBorchersSequence d) :
    ((F + G : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) + (G : BorchersSequence d) := rfl

@[simp] theorem neg_toBorchersSequence (F : PositiveTimeBorchersSequence d) :
    ((-F : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      - (F : BorchersSequence d) := rfl

@[simp] theorem smul_toBorchersSequence (c : ℂ) (F : PositiveTimeBorchersSequence d) :
    ((c • F : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      c • (F : BorchersSequence d) := rfl

@[simp] theorem sub_toBorchersSequence (F G : PositiveTimeBorchersSequence d) :
    ((F - G : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) - (G : BorchersSequence d) := rfl

@[simp] theorem single_toBorchersSequence (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n) :
    ((single n f hf : PositiveTimeBorchersSequence d) : BorchersSequence d) =
      BorchersSequence.single n f := rfl

/-- On the honest positive-time Euclidean Borchers algebra, OS tensor terms are
    automatically zero-diagonal admissible. -/
theorem ostensorAdmissible [NeZero d] (F G : PositiveTimeBorchersSequence d) :
    OSTensorAdmissible d (F : BorchersSequence d) (G : BorchersSequence d) :=
  OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
    (d := d) (F : BorchersSequence d) (G : BorchersSequence d)
    F.ordered_tsupport G.ordered_tsupport

end PositiveTimeBorchersSequence

/-- Pointwise block-swap identity for the OS-conjugated tensor product.

    This is the OS analogue of `conjTP_eq_borchersConj_conjTP`: applying the
    OS involution to `g.osConjTensorProduct f` swaps the two tensor blocks and
    yields `f.osConjTensorProduct g` after the canonical `n + m = m + n`
    reindexing. -/
private theorem osConjTP_eq_osConj_osConjTP {d n m : ℕ} [NeZero d]
    (f : SchwartzNPoint d m) (g : SchwartzNPoint d n)
    (x : NPointDomain d (n + m)) :
    ((g.osConjTensorProduct f).osConj) x =
      (f.osConjTensorProduct g) (fun i => x (finAddFlip i)) := by
  have hfarg :
      splitLast n m (timeReflectionN d x) =
        timeReflectionN d (splitFirst m n (fun i => x (finAddFlip i))) := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitFirst, splitLast, timeReflectionN, timeReflection,
        finAddFlip_apply_castAdd]
    · simp [splitFirst, splitLast, timeReflectionN, timeReflection, hμ,
        finAddFlip_apply_castAdd]
  have hgarg :
      timeReflectionN d (splitFirst n m (timeReflectionN d x)) =
        splitLast m n (fun i => x (finAddFlip i)) := by
    ext k μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitFirst, splitLast, timeReflectionN, timeReflection,
        finAddFlip_apply_natAdd]
    · simp [splitFirst, splitLast, timeReflectionN, timeReflection, hμ,
        finAddFlip_apply_natAdd]
  simp only [SchwartzNPoint.osConj_apply, SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply, map_mul, starRingEnd_self_apply]
  rw [mul_comm]
  rw [hfarg, hgarg]

/-- Extending the second OS summation range does not change the value. -/
theorem OSInnerProductN_extend_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₂ : G.bound + 1 ≤ N₂) :
    OSInnerProductN d S F G N₁ N₂ = OSInnerProductN d S F G N₁ (G.bound + 1) := by
  unfold OSInnerProductN
  apply Finset.sum_congr rfl
  intro n _
  symm
  apply Finset.sum_subset (Finset.range_mono hN₂)
  intro m hm₂ hm₁
  have hm : G.bound < m := by
    simp only [Finset.mem_range] at hm₁ hm₂
    omega
  rw [G.bound_spec m hm, SchwartzNPoint.osConjTensorProduct_zero_right,
    ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]

/-- Extending the first OS summation range does not change the value. -/
theorem OSInnerProductN_extend_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) :
    OSInnerProductN d S F G N₁ N₂ = OSInnerProductN d S F G (F.bound + 1) N₂ := by
  unfold OSInnerProductN
  symm
  apply Finset.sum_subset (Finset.range_mono hN₁)
  intro n hn₂ hn₁
  have hn : F.bound < n := by
    simp only [Finset.mem_range] at hn₁ hn₂
    omega
  apply Finset.sum_eq_zero
  intro m _
  rw [F.bound_spec n hn, SchwartzNPoint.osConjTensorProduct_zero_left,
    ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]

/-- The OS inner product can be computed using any sufficiently large bounds. -/
theorem OSInnerProduct_eq_extended (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G : BorchersSequence d) (N₁ N₂ : ℕ)
    (hN₁ : F.bound + 1 ≤ N₁) (hN₂ : G.bound + 1 ≤ N₂) :
    OSInnerProduct d S F G = OSInnerProductN d S F G N₁ N₂ := by
  rw [OSInnerProduct_eq_N,
    ← OSInnerProductN_extend_right d S hlin F G (F.bound + 1) N₂ hN₂,
    ← OSInnerProductN_extend_left d S hlin F G N₁ N₂ hN₁]

/-- For concentrated Borchers sequences, the OS inner product reduces to the
single tensor term. -/
theorem OSInnerProduct_single_single (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    OSInnerProduct d S (BorchersSequence.single n f) (BorchersSequence.single m g) =
      S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  unfold OSInnerProduct
  rw [BorchersSequence.single_bound, BorchersSequence.single_bound, Finset.sum_range_succ]
  have hleft :
      ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range (m + 1),
          S (i + j) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs i).osConjTensorProduct
              ((BorchersSequence.single m g).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_ne : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
    apply Finset.sum_eq_zero
    intro j hj
    rw [BorchersSequence.single_funcs_ne hi_ne, SchwartzNPoint.osConjTensorProduct_zero_left,
      ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]
  rw [hleft, zero_add, BorchersSequence.single_funcs_eq, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        S (n + j) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct ((BorchersSequence.single m g).funcs j))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_zero, (hlin _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]

/-- The OS inner product depends only on `funcs`, not on `bound`. -/
theorem OSInnerProduct_congr_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G₁ G₂ : BorchersSequence d)
    (h : ∀ n, G₁.funcs n = G₂.funcs n) :
    OSInnerProduct d S F G₁ = OSInnerProduct d S F G₂ := by
  rw [OSInnerProduct_eq_extended d S hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_left _ _)),
      OSInnerProduct_eq_extended d S hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) le_rfl
        (Nat.succ_le_succ (le_max_right _ _))]
  simp only [OSInnerProductN]
  congr 1
  ext n
  congr 1
  ext m
  rw [h m]

/-- The OS inner product depends only on `funcs`, not on `bound` (left argument). -/
theorem OSInnerProduct_congr_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F₁ F₂ G : BorchersSequence d)
    (h : ∀ n, F₁.funcs n = F₂.funcs n) :
    OSInnerProduct d S F₁ G = OSInnerProduct d S F₂ G := by
  rw [OSInnerProduct_eq_extended d S hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_left _ _)) le_rfl,
      OSInnerProduct_eq_extended d S hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1)
        (Nat.succ_le_succ (le_max_right _ _)) le_rfl]
  simp only [OSInnerProductN]
  congr 1
  ext n
  congr 1
  ext m
  rw [h n]

/-- The OS inner product with zero in the right argument vanishes. -/
theorem OSInnerProduct_zero_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F : BorchersSequence d) :
    OSInnerProduct d S F 0 = 0 := by
  unfold OSInnerProduct
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct ((0 : BorchersSequence d).funcs m)) = 0 := by
    rw [BorchersSequence.zero_funcs, SchwartzNPoint.osConjTensorProduct_zero_right,
      ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := (0 : SchwartzNPoint d (n + m)))
        (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))]
    rfl
  rw [hzero]
  exact (hlin _).map_zero

/-- The OS inner product with zero in the left argument vanishes. -/
theorem OSInnerProduct_zero_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (G : BorchersSequence d) :
    OSInnerProduct d S 0 G = 0 := by
  unfold OSInnerProduct
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
        (((0 : BorchersSequence d).funcs n).osConjTensorProduct (G.funcs m)) = 0 := by
    rw [BorchersSequence.zero_funcs, SchwartzNPoint.osConjTensorProduct_zero_left,
      ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := (0 : SchwartzNPoint d (n + m)))
        (VanishesToInfiniteOrderOnCoincidence.zero (d := d) (n := n + m))]
    rfl
  rw [hzero]
  exact (hlin _).map_zero

/-- The OS inner product is additive in the second argument. -/
theorem OSInnerProduct_add_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F G₁ G₂ : BorchersSequence d)
    (hFG₁ : OSTensorAdmissible d F G₁)
    (hFG₂ : OSTensorAdmissible d F G₂) :
    OSInnerProduct d S F (G₁ + G₂) =
      OSInnerProduct d S F G₁ + OSInnerProduct d S F G₂ := by
  have hN₁ : F.bound + 1 ≤ F.bound + 1 := le_rfl
  have hN₂_sum : (G₁ + G₂).bound + 1 ≤ max G₁.bound G₂.bound + 1 := le_rfl
  have hN₂_1 : G₁.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₂_2 : G₂.bound + 1 ≤ max G₁.bound G₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  rw [OSInnerProduct_eq_extended d S hlin F (G₁ + G₂)
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_sum,
      OSInnerProduct_eq_extended d S hlin F G₁
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_1,
      OSInnerProduct_eq_extended d S hlin F G₂
        (F.bound + 1) (max G₁.bound G₂.bound + 1) hN₁ hN₂_2]
  unfold OSInnerProductN
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hsum :=
    ZeroDiagonalSchwartz.ofClassical_add_of_vanishes
      ((F.funcs n).osConjTensorProduct (G₁.funcs m))
      ((F.funcs n).osConjTensorProduct (G₂.funcs m))
      (hFG₁ n m) (hFG₂ n m)
  rw [BorchersSequence.add_funcs,
    SchwartzNPoint.osConjTensorProduct_add_right, hsum, (hlin _).map_add]

/-- The OS inner product is additive in the first argument. -/
theorem OSInnerProduct_add_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F₁ F₂ G : BorchersSequence d)
    (hF₁G : OSTensorAdmissible d F₁ G)
    (hF₂G : OSTensorAdmissible d F₂ G) :
    OSInnerProduct d S (F₁ + F₂) G =
      OSInnerProduct d S F₁ G + OSInnerProduct d S F₂ G := by
  have hN₁_sum : (F₁ + F₂).bound + 1 ≤ max F₁.bound F₂.bound + 1 := le_rfl
  have hN₁_1 : F₁.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_left _ _)
  have hN₁_2 : F₂.bound + 1 ≤ max F₁.bound F₂.bound + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  have hN₂ : G.bound + 1 ≤ G.bound + 1 := le_rfl
  rw [OSInnerProduct_eq_extended d S hlin (F₁ + F₂) G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_sum hN₂,
      OSInnerProduct_eq_extended d S hlin F₁ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_1 hN₂,
      OSInnerProduct_eq_extended d S hlin F₂ G
        (max F₁.bound F₂.bound + 1) (G.bound + 1) hN₁_2 hN₂]
  unfold OSInnerProductN
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have hsum :=
    ZeroDiagonalSchwartz.ofClassical_add_of_vanishes
      ((F₁.funcs n).osConjTensorProduct (G.funcs m))
      ((F₂.funcs n).osConjTensorProduct (G.funcs m))
      (hF₁G n m) (hF₂G n m)
  rw [BorchersSequence.add_funcs,
    SchwartzNPoint.osConjTensorProduct_add_left, hsum, (hlin _).map_add]

/-- The OS inner product is linear in the second argument. -/
theorem OSInnerProduct_smul_right (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (c : ℂ) (F G : BorchersSequence d) :
    OSInnerProduct d S F (c • G) = c * OSInnerProduct d S F G := by
  simp only [OSInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound]
  simp_rw [SchwartzNPoint.osConjTensorProduct_smul_right,
    ZeroDiagonalSchwartz.ofClassical_smul, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext n
  rw [Finset.mul_sum]

/-- The OS inner product is conjugate linear in the first argument. -/
theorem OSInnerProduct_smul_left (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (c : ℂ) (F G : BorchersSequence d) :
    OSInnerProduct d S (c • F) G = starRingEnd ℂ c * OSInnerProduct d S F G := by
  simp only [OSInnerProduct, BorchersSequence.smul_funcs, BorchersSequence.smul_bound]
  simp_rw [SchwartzNPoint.osConjTensorProduct_smul_left,
    ZeroDiagonalSchwartz.ofClassical_smul, (hlin _).map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext n
  rw [Finset.mul_sum]

/-- The Osterwalder-Schrader axioms E0-E4 for Euclidean field theory.

    From OS I (1973):
    - E0: Temperedness (Sₙ ∈ S'(ℝ^{dn}))
    - E1: Euclidean invariance
    - E2: Reflection positivity: Σₙ,ₘ Sₙ₊ₘ(Θf* × fₘ) ≥ 0 for f ∈ S₊
    - E3: Symmetry: Sₙ(f) = Sₙ(f^π) for all permutations π
    - E4: Cluster property

    **Important**: As shown in OS II (1975), these axioms alone may NOT be
    sufficient to reconstruct a Wightman QFT. The linear growth condition E0'
    is needed. See `OSLinearGrowthCondition`.

    **Critical correction**: the heart of OS reconstruction is precisely the
    passage from Euclidean data defined only on the zero-diagonal test space
    `°S` to full tempered Wightman distributions on Schwartz space. The Euclidean
    starting point must therefore be stated on `ZeroDiagonalSchwartz` itself,
    not on a fictitious full-Schwartz Schwinger theory. -/
structure OsterwalderSchraderAxioms (d : ℕ) [NeZero d] where
  /-- The honest zero-diagonal Euclidean Schwinger family. -/
  S : SchwingerFunctions d
  /-- E0: Temperedness on the OS-I zero-diagonal test space `°S`.

      The literal OS-I Schwinger functions are distributions on the coincidence-free
      test space, not a priori on the full Schwartz space. Any later extension to
      all of `SchwartzNPoint` is extra structure beyond this axiom surface.

      The point is that inverse-power coincidence singularities are compatible
      with `°S`: zero-diagonal test functions vanish to arbitrarily high order on
      the coincidence locus, so kernels of finite singular order still define the
      honest Euclidean pairing there. This is why the corrected OS axiom is stated
      on `ZeroDiagonalSchwartz`, not on full Schwartz space. -/
  E0_tempered : ∀ n, Continuous (S n)
  /-- E0 also includes linearity on the honest Euclidean test space `°S`. -/
  E0_linear : ∀ n, IsLinearMap ℂ (S n)
  /-- E0 also includes the Schwinger reality condition induced by Wightman
      Hermiticity:
      `conj (S_n(f)) = S_n(f.osConj)`.

      The transformed test function is supplied as a zero-diagonal witness rather
      than by asserting a full-Schwartz Euclidean theory. -/
  E0_reality : ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
    starRingEnd ℂ (S n f) = S n g
  /-- E1a: Translation invariance.
      S_n(x₁+a,...,xₙ+a) = S_n(x₁,...,xₙ) for all a ∈ ℝ^{d+1}. -/
  E1_translation_invariant : ∀ (n : ℕ) (a : SpacetimeDim d)
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x i + a)) →
    S n f = S n g
  /-- E1b: Rotation invariance under SO(d+1).
      S_n(Rx₁,...,Rxₙ) = S_n(x₁,...,xₙ) for all R ∈ SO(d+1).
      Together with E1a, this gives Euclidean covariance under ℝ^{d+1} ⋊ SO(d+1).
      Note: Full O(d+1) invariance (including improper rotations with det=-1)
      would require parity invariance, which is not implied by the Wightman axioms. -/
  E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    R.transpose * R = 1 → R.det = 1 →
    ∀ (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
    S n f = S n g
  /-- E2: Reflection positivity - the crucial axiom for Hilbert space construction.
      For test functions whose topological support lies in the OS-I ordered positive-time region
      `0 < x₁⁰ < ... < xₙ⁰`,
      `Σₙ,ₘ S_{n+m}(θf̄ₙ ⊗ fₘ) ≥ 0`
      where θ is time reflection θ(τ,x⃗) = (-τ,x⃗) and f̄ is complex conjugation.
      This uses `OSInnerProduct` (time reflection + conjugation), the correct
      inner product for the Euclidean framework.
      This ensures the reconstructed inner product is positive definite. -/
  E2_reflection_positive : ∀ (F : BorchersSequence d),
    (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) →
    (OSInnerProduct d S F F).re ≥ 0
  /-- E3: Permutation symmetry - Schwinger functions are symmetric under
      permutation of arguments: S_n(x_{σ(1)},...,x_{σ(n)}) = S_n(x₁,...,xₙ)
      for all permutations σ ∈ Sₙ. -/
  E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f g : ZeroDiagonalSchwartz d n),
    (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
    S n f = S n g
  /-- E4: Cluster property - factorization at large separations.
      lim_{|a|→∞} S_{n+m}(x₁,...,xₙ,y₁+a,...,yₘ+a) = S_n(x₁,...,xₙ) · S_m(y₁,...,yₘ)
      This reflects the uniqueness of the vacuum in the reconstructed theory.

      Expressed via the connected n-point functions: the connected part Sₙᶜ vanishes
      for n ≥ 2 at large separations. Equivalently, for product test functions
      with widely separated supports, S_{n+m} factorizes. -/
  E4_cluster : ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m),
    -- Cluster property: as spatial separation increases, S_{n+m} factorizes.
    -- For any ε > 0, there exists R > 0 such that for spatial translation a with |a| > R,
    -- |S_{n+m}(f ⊗ τ_a g) - S_n(f) · S_m(g)| < ε
    -- where τ_a g is g translated by a in all m coordinates.
    -- The translation a must be purely spatial (a 0 = 0): Euclidean time shifts
    -- correspond to imaginary Minkowski time, leaving the cluster property's domain.
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        -- For any Schwartz function g_a that is the translation of g by a:
        ∀ (g_a : ZeroDiagonalSchwartz d m),
          (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
            (∀ x : NPointDomain d (n + m),
              fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
            ‖S (n + m) fg_a - S n f * S m g‖ < ε

/-- The abstract OS inner product is Hermitian.

    This is the Euclidean analogue of `WightmanInnerProduct_hermitian`. The
    proof uses only the corrected OS reality condition together with
    permutation symmetry to swap the tensor blocks after applying the OS
    involution. -/
private theorem cast_zeroDiagonalSchwartz_apply {d k₁ k₂ : ℕ}
    (hk : k₁ = k₂) (f : ZeroDiagonalSchwartz d k₁) (x : NPointDomain d k₂) :
    (cast (congrArg (ZeroDiagonalSchwartz d) hk) f).1 x =
      f.1 (fun i => x (Fin.cast hk i)) := by
  cases hk
  rfl

private theorem S_eq_of_cast {d : ℕ}
    (S : (k : ℕ) → ZeroDiagonalSchwartz d k → ℂ)
    (k₁ k₂ : ℕ) (hk : k₁ = k₂)
    (f : ZeroDiagonalSchwartz d k₁) (g : ZeroDiagonalSchwartz d k₂)
    (hfg : ∀ x, f.1 x = g.1 (fun i => x (Fin.cast hk.symm i))) :
    S k₁ f = S k₂ g := by
  subst hk
  have hfg' : f = g := by
    apply Subtype.ext
    ext x
    simpa using hfg x
  simpa [hfg']

private def blockSwapPerm (m n : ℕ) : Equiv.Perm (Fin (n + m)) where
  toFun := fun i =>
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Fin.cast (Nat.add_comm m n).symm i)
  invFun := fun i =>
    Fin.cast (Nat.add_comm m n)
      ((finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm i)
  left_inv := by
    intro i
    simp
  right_inv := by
    intro i
    simp

@[simp] private theorem blockSwapPerm_cast_eq_finAddFlip {m n : ℕ}
    (i : Fin (m + n)) :
    blockSwapPerm m n (Fin.cast (Nat.add_comm m n) i) =
      (finAddFlip : Fin (m + n) ≃ Fin (n + m)) i := by
  simp [blockSwapPerm]

theorem OSInnerProduct_hermitian {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (F G : BorchersSequence d)
    (hFG : OSTensorAdmissible d F G)
    (hGF : OSTensorAdmissible d G F) :
    OSInnerProduct d OS.S F G = starRingEnd ℂ (OSInnerProduct d OS.S G F) := by
  simp only [OSInnerProduct, map_sum]
  rw [Finset.sum_comm]
  congr 1
  ext n
  congr 1
  ext m
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := (F.funcs m).osConjTensorProduct (G.funcs n)) (hFG m n),
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := (G.funcs n).osConjTensorProduct (F.funcs m)) (hGF n m)]
  let A : ZeroDiagonalSchwartz d (n + m) :=
    ⟨(G.funcs n).osConjTensorProduct (F.funcs m), hGF n m⟩
  let C' : ZeroDiagonalSchwartz d (m + n) :=
    ⟨(F.funcs m).osConjTensorProduct (G.funcs n), hFG m n⟩
  let C : ZeroDiagonalSchwartz d (n + m) :=
    cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C'
  let B : ZeroDiagonalSchwartz d (n + m) :=
    ⟨reindexSchwartz (d := d) (σ := (finAddFlip : Fin (m + n) ≃ Fin (n + m))) C'.1,
      VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
        (d := d) (f := C'.1) C'.2
        (finAddFlip : Fin (m + n) ≃ Fin (n + m))⟩
  have hreal : starRingEnd ℂ (OS.S (n + m) A) = OS.S (n + m) B := by
    refine OS.E0_reality (n := n + m) (f := A) (g := B) ?_
    intro x
    simpa [A, B, C', reindexSchwartz_apply, SchwartzNPoint.osConj_apply] using
      (osConjTP_eq_osConj_osConjTP (d := d) (n := n) (m := m)
        (f := F.funcs m) (g := G.funcs n) x).symm
  have hcast : OS.S (m + n) C' = OS.S (n + m) C := by
    refine S_eq_of_cast OS.S (m + n) (n + m) (Nat.add_comm m n) C' C ?_
    intro x
    rw [show C = cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C' by rfl]
    rw [cast_zeroDiagonalSchwartz_apply (hk := Nat.add_comm m n) (f := C')
      (x := fun i => x (Fin.cast (Nat.add_comm m n).symm i))]
    simp
  have hperm : OS.S (n + m) C = OS.S (n + m) B := by
    refine OS.E3_symmetric (n := n + m) (σ := blockSwapPerm m n) (f := C) (g := B) ?_
    intro x
    rw [show C = cast (congrArg (ZeroDiagonalSchwartz d) (Nat.add_comm m n)) C' by rfl]
    rw [cast_zeroDiagonalSchwartz_apply (hk := Nat.add_comm m n) (f := C')
      (x := fun i => x (blockSwapPerm m n i))]
    simp [B, C', reindexSchwartz_apply]
  calc
    OS.S (m + n) C' = OS.S (n + m) C := hcast
    _ = OS.S (n + m) B := hperm
    _ = starRingEnd ℂ (OS.S (n + m) A) := hreal.symm

/-- The linear growth condition E0' from OS II (1975).

    This replaces the simple temperedness E0 with a stronger condition:
    There exist s ∈ ℤ₊ and constants α, β, γ such that for σₙ ≤ αβⁿ(n!)^γ,
      |Sₙ(f)| ≤ σₙ ‖f‖_{s,n}

    This condition controls the growth of the distribution order as n → ∞,
    which is essential for proving temperedness of the reconstructed
    Wightman distributions.

    The key point is that this growth hypothesis belongs on the Euclidean side
    before reconstruction; it does not erase the main difficulty. The theorem
    still has to manufacture full tempered Wightman distributions starting only
    from Schwinger data whose honest Euclidean test space is `°S`. -/
structure OSLinearGrowthCondition (d : ℕ) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  /-- E0' normalization at zero points: `S₀(f) = f(0)`. -/
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
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
  growth_estimate : ∀ (n : ℕ) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      SchwartzMap.seminorm ℝ sobolev_index sobolev_index f.1

/-- The honest zero-diagonal Schwinger family underlying an OS package.

    Public reconstruction theorems should be stated in terms of this actual
    Euclidean datum on `ZeroDiagonalSchwartz`. -/
def OsterwalderSchraderAxioms.schwinger {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) : SchwingerFunctions d :=
  OS.S

namespace PositiveTimeBorchersSequence

variable {d : ℕ} [NeZero d]

/-- The OS sesquilinear form on the honest positive-time Euclidean Borchers algebra. -/
def osInner (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) : ℂ :=
  OSInnerProduct d OS.S (F : BorchersSequence d) (G : BorchersSequence d)

@[simp] theorem osInner_zero_right (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    osInner OS F 0 = 0 := by
  unfold osInner
  simpa using OSInnerProduct_zero_right (d := d) OS.S OS.E0_linear (F : BorchersSequence d)

@[simp] theorem osInner_zero_left (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    osInner OS 0 F = 0 := by
  unfold osInner
  simpa using OSInnerProduct_zero_left (d := d) OS.S OS.E0_linear (F : BorchersSequence d)

theorem osInner_add_right (OS : OsterwalderSchraderAxioms d)
    (F G₁ G₂ : PositiveTimeBorchersSequence d) :
    osInner OS F (G₁ + G₂) = osInner OS F G₁ + osInner OS F G₂ := by
  unfold osInner
  simpa using OSInnerProduct_add_right (d := d) OS.S OS.E0_linear
    (F : BorchersSequence d) (G₁ : BorchersSequence d) (G₂ : BorchersSequence d)
    (ostensorAdmissible F G₁) (ostensorAdmissible F G₂)

theorem osInner_add_left (OS : OsterwalderSchraderAxioms d)
    (F₁ F₂ G : PositiveTimeBorchersSequence d) :
    osInner OS (F₁ + F₂) G = osInner OS F₁ G + osInner OS F₂ G := by
  unfold osInner
  simpa using OSInnerProduct_add_left (d := d) OS.S OS.E0_linear
    (F₁ : BorchersSequence d) (F₂ : BorchersSequence d) (G : BorchersSequence d)
    (ostensorAdmissible F₁ G) (ostensorAdmissible F₂ G)

theorem osInner_smul_right (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F G : PositiveTimeBorchersSequence d) :
    osInner OS F (c • G) = c * osInner OS F G := by
  unfold osInner
  simpa using OSInnerProduct_smul_right (d := d) OS.S OS.E0_linear
    c (F : BorchersSequence d) (G : BorchersSequence d)

theorem osInner_smul_left (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F G : PositiveTimeBorchersSequence d) :
    osInner OS (c • F) G = starRingEnd ℂ c * osInner OS F G := by
  unfold osInner
  simpa using OSInnerProduct_smul_left (d := d) OS.S OS.E0_linear
    c (F : BorchersSequence d) (G : BorchersSequence d)

theorem osInner_neg_right (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS F (-G) = -osInner OS F G := by
  have hcongr :
      osInner OS F (-G) = osInner OS F ((-1 : ℂ) • G) := by
    unfold osInner
    refine OSInnerProduct_congr_right d OS.S OS.E0_linear
      (F : BorchersSequence d)
      ((-G : PositiveTimeBorchersSequence d) : BorchersSequence d)
      ((((-1 : ℂ) • G : PositiveTimeBorchersSequence d)) : BorchersSequence d) ?_
    intro n
    simpa [BorchersSequence.neg_funcs, BorchersSequence.smul_funcs] using
      (neg_one_smul ((G : BorchersSequence d).funcs n : SchwartzNPoint d n))
  rw [hcongr, osInner_smul_right]
  ring

theorem osInner_neg_left (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS (-F) G = -osInner OS F G := by
  have hcongr :
      osInner OS (-F) G = osInner OS ((-1 : ℂ) • F) G := by
    unfold osInner
    refine OSInnerProduct_congr_left d OS.S OS.E0_linear
      ((-F : PositiveTimeBorchersSequence d) : BorchersSequence d)
      ((((-1 : ℂ) • F : PositiveTimeBorchersSequence d)) : BorchersSequence d)
      (G : BorchersSequence d) ?_
    intro n
    simpa [BorchersSequence.neg_funcs, BorchersSequence.smul_funcs] using
      (neg_one_smul ((F : BorchersSequence d).funcs n : SchwartzNPoint d n))
  rw [hcongr, osInner_smul_left]
  simp

theorem osInner_sub_right (OS : OsterwalderSchraderAxioms d)
    (F G₁ G₂ : PositiveTimeBorchersSequence d) :
    osInner OS F (G₁ - G₂) = osInner OS F G₁ - osInner OS F G₂ := by
  calc
    osInner OS F (G₁ - G₂) = osInner OS F (G₁ + -G₂) := by rfl
    _ = osInner OS F G₁ + osInner OS F (-G₂) := osInner_add_right OS F G₁ (-G₂)
    _ = osInner OS F G₁ + (-osInner OS F G₂) := by rw [osInner_neg_right]
    _ = osInner OS F G₁ - osInner OS F G₂ := by ring

theorem osInner_sub_left (OS : OsterwalderSchraderAxioms d)
    (F₁ F₂ G : PositiveTimeBorchersSequence d) :
    osInner OS (F₁ - F₂) G = osInner OS F₁ G - osInner OS F₂ G := by
  calc
    osInner OS (F₁ - F₂) G = osInner OS (F₁ + -F₂) G := by rfl
    _ = osInner OS F₁ G + osInner OS (-F₂) G := osInner_add_left OS F₁ (-F₂) G
    _ = osInner OS F₁ G + (-osInner OS F₂ G) := by rw [osInner_neg_left]
    _ = osInner OS F₁ G - osInner OS F₂ G := by ring

theorem osInner_hermitian (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS F G = starRingEnd ℂ (osInner OS G F) := by
  unfold osInner
  simpa using OSInnerProduct_hermitian (d := d) OS
    (F : BorchersSequence d) (G : BorchersSequence d)
    (ostensorAdmissible F G) (ostensorAdmissible G F)

theorem osInner_nonneg_self (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ (osInner OS F F).re :=
  OS.E2_reflection_positive (F : BorchersSequence d) F.ordered_tsupport

private theorem osInner_quadratic_re (OS : OsterwalderSchraderAxioms d)
    (X Y : PositiveTimeBorchersSequence d) (t : ℝ) :
    (osInner OS (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re =
    (osInner OS X X).re +
      2 * (osInner OS X Y).re * t +
      (osInner OS Y Y).re * t ^ 2 := by
  rw [osInner_add_left, osInner_add_right, osInner_add_right,
    osInner_smul_right, osInner_smul_left, osInner_smul_left, osInner_smul_right,
    osInner_hermitian]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
  have hherm_re : (osInner OS Y X).re = (osInner OS X Y).re := by
    have h := congrArg Complex.re (osInner_hermitian OS X Y)
    simpa using h.symm
  rw [hherm_re]
  ring

/-- Null vectors for the honest positive-time OS form are orthogonal to every
    positive-time Borchers vector. This is the Euclidean analogue of
    `null_inner_product_zero` on the Wightman side and is the key algebraic input
    for an honest OS GNS quotient. -/
theorem null_osInner_zero (OS : OsterwalderSchraderAxioms d)
    (X Y : PositiveTimeBorchersSequence d)
    (hX : (osInner OS X X).re = 0) :
    osInner OS X Y = 0 := by
  set w := osInner OS X Y with hw
  have hre : w.re = 0 := by
    apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
    rw [mul_zero]
    apply quadratic_nonneg_linear_zero (osInner OS Y Y).re
    · exact osInner_nonneg_self OS Y
    · intro t
      rw [show (osInner OS Y Y).re * t ^ 2 + 2 * w.re * t =
          (osInner OS (X + (↑t : ℂ) • Y) (X + (↑t : ℂ) • Y)).re from by
            rw [osInner_quadratic_re, hX]
            ring]
      exact osInner_nonneg_self OS (X + (↑t : ℂ) • Y)
  have him : w.im = 0 := by
    have hIw : osInner OS X (Complex.I • Y) = Complex.I * w := by
      rw [osInner_smul_right]
    have hIw_re : (Complex.I * w).re = -w.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have hre_Z : (osInner OS X (Complex.I • Y)).re = 0 := by
      apply mul_left_cancel₀ (two_ne_zero (α := ℝ))
      rw [mul_zero]
      apply quadratic_nonneg_linear_zero (osInner OS (Complex.I • Y) (Complex.I • Y)).re
      · exact osInner_nonneg_self OS (Complex.I • Y)
      · intro t
        rw [show (osInner OS (Complex.I • Y) (Complex.I • Y)).re * t ^ 2 +
            2 * (osInner OS X (Complex.I • Y)).re * t =
            (osInner OS (X + (↑t : ℂ) • (Complex.I • Y))
              (X + (↑t : ℂ) • (Complex.I • Y))).re from by
              rw [osInner_quadratic_re, hX]
              ring]
        exact osInner_nonneg_self OS (X + (↑t : ℂ) • (Complex.I • Y))
    rw [hIw, hIw_re] at hre_Z
    linarith
  exact Complex.ext hre him

theorem osInner_expand_diff (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    osInner OS (F - G) (F - G) =
      osInner OS F F + osInner OS G G - osInner OS F G - osInner OS G F := by
  rw [osInner_sub_left, osInner_sub_right, osInner_sub_right]
  ring

end PositiveTimeBorchersSequence

/-- The honest OS null-space relation on the positive-time Euclidean Borchers algebra.
    Two vectors are equivalent iff their difference has zero OS norm. -/
def osBorchersSetoid {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) :
    Setoid (PositiveTimeBorchersSequence d) where
  r F G := (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re = 0
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro F
      rw [PositiveTimeBorchersSequence.osInner_expand_diff]
      ring_nf
      simp
    · intro F G hFG
      have hfuncs_neg :
          ∀ n,
            (((G - F : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
              (((-(F - G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
        intro n
        simp [sub_eq_add_neg]
      have hneg :
          PositiveTimeBorchersSequence.osInner OS (G - F) (G - F) =
            PositiveTimeBorchersSequence.osInner OS (-(F - G)) (-(F - G)) := by
        unfold PositiveTimeBorchersSequence.osInner
        exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs_neg).trans
          (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs_neg)
      have hsymm :
          (PositiveTimeBorchersSequence.osInner OS (G - F) (G - F)).re =
            (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re := by
        rw [hneg, PositiveTimeBorchersSequence.osInner_neg_left,
          PositiveTimeBorchersSequence.osInner_neg_right, neg_neg]
      exact hsymm.trans hFG
    · intro F G H hFG hGH
      let A : PositiveTimeBorchersSequence d := F - G
      let B : PositiveTimeBorchersSequence d := G - H
      have hA : PositiveTimeBorchersSequence.osInner OS A A = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS A A hFG
      have hB : PositiveTimeBorchersSequence.osInner OS B B = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS B B hGH
      have hAB : PositiveTimeBorchersSequence.osInner OS A B = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS A B hFG
      have hBA : PositiveTimeBorchersSequence.osInner OS B A = 0 :=
        PositiveTimeBorchersSequence.null_osInner_zero OS B A hGH
      have hsum :
          PositiveTimeBorchersSequence.osInner OS (A + B) (A + B) = 0 := by
        rw [PositiveTimeBorchersSequence.osInner_add_left,
          PositiveTimeBorchersSequence.osInner_add_right,
          PositiveTimeBorchersSequence.osInner_add_right, hA, hAB, hBA, hB]
        ring
      have hkey :
          ∀ n,
            (((F - H : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
              (((A + B : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
        intro n
        simp [A, B, sub_eq_add_neg]
        abel
      have hFH :
          PositiveTimeBorchersSequence.osInner OS (F - H) (F - H) =
            PositiveTimeBorchersSequence.osInner OS (A + B) (A + B) := by
        unfold PositiveTimeBorchersSequence.osInner
        exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hkey).trans
          (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hkey)
      rw [hFH]
      exact congrArg Complex.re hsum

/-- The honest Euclidean pre-Hilbert space: quotient of positive-time Borchers
    sequences by the OS null space. -/
def OSPreHilbertSpace {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) : Type :=
  Quotient (osBorchersSetoid OS)

/-- The OS inner product on the Euclidean GNS quotient. -/
def OSPreHilbertSpace.innerProduct {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d) :
    OSPreHilbertSpace OS → OSPreHilbertSpace OS → ℂ :=
  Quotient.lift₂ (PositiveTimeBorchersSequence.osInner OS) (by
    intro a₁ a₂ b₁ b₂ ha hb
    have ha_eq :
        ∀ G : PositiveTimeBorchersSequence d,
          PositiveTimeBorchersSequence.osInner OS a₁ G =
            PositiveTimeBorchersSequence.osInner OS b₁ G := by
      intro G
      have h := PositiveTimeBorchersSequence.null_osInner_zero OS (a₁ - b₁) G ha
      rwa [PositiveTimeBorchersSequence.osInner_sub_left, sub_eq_zero] at h
    have hb_eq :
        ∀ F : PositiveTimeBorchersSequence d,
          PositiveTimeBorchersSequence.osInner OS F a₂ =
            PositiveTimeBorchersSequence.osInner OS F b₂ := by
      intro F
      have h := PositiveTimeBorchersSequence.null_osInner_zero OS (a₂ - b₂) F hb
      rw [PositiveTimeBorchersSequence.osInner_sub_left, sub_eq_zero] at h
      calc
        PositiveTimeBorchersSequence.osInner OS F a₂ =
            starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS a₂ F) := by
              rw [PositiveTimeBorchersSequence.osInner_hermitian]
        _ = starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS b₂ F) := by rw [h]
        _ = starRingEnd ℂ (starRingEnd ℂ (PositiveTimeBorchersSequence.osInner OS F b₂)) := by
              rw [PositiveTimeBorchersSequence.osInner_hermitian]
        _ = PositiveTimeBorchersSequence.osInner OS F b₂ := by simp
    rw [ha_eq a₂, hb_eq b₁])

namespace OSPreHilbertSpace

variable {d : ℕ} [NeZero d] (OS : OsterwalderSchraderAxioms d)

/-- Two positive-time Borchers sequences with identical components represent the
    same class in the honest OS quotient. -/
theorem osBorchersSetoid_of_funcs_eq (F G : PositiveTimeBorchersSequence d)
    (h : ∀ n, ((F : BorchersSequence d).funcs n) = ((G : BorchersSequence d).funcs n)) :
    osBorchersSetoid OS F G := by
  show (PositiveTimeBorchersSequence.osInner OS (F - G) (F - G)).re = 0
  have hzero :
      ∀ n,
        (((F - G : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((0 : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [h n]
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS (F - G) (F - G) =
        PositiveTimeBorchersSequence.osInner OS 0 0 := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hzero).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hzero)
  rw [hcongr]
  simp

/-- Addition respects the OS null relation. -/
theorem add_respects_equiv (F₁ G₁ F₂ G₂ : PositiveTimeBorchersSequence d)
    (h₁ : osBorchersSetoid OS F₁ G₁) (h₂ : osBorchersSetoid OS F₂ G₂) :
    osBorchersSetoid OS (F₁ + F₂) (G₁ + G₂) := by
  have h1_null : PositiveTimeBorchersSequence.osInner OS (F₁ - G₁) (F₁ - G₁) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₁ - G₁) (F₁ - G₁) h₁
  have h2_null : PositiveTimeBorchersSequence.osInner OS (F₂ - G₂) (F₂ - G₂) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₂ - G₂) (F₂ - G₂) h₂
  have h12_null : PositiveTimeBorchersSequence.osInner OS (F₁ - G₁) (F₂ - G₂) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₁ - G₁) (F₂ - G₂) h₁
  have h21_null : PositiveTimeBorchersSequence.osInner OS (F₂ - G₂) (F₁ - G₁) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F₂ - G₂) (F₁ - G₁) h₂
  show (PositiveTimeBorchersSequence.osInner OS
    ((F₁ + F₂) - (G₁ + G₂)) ((F₁ + F₂) - (G₁ + G₂))).re = 0
  have hfuncs :
      ∀ n,
        ((((F₁ + F₂) - (G₁ + G₂) : PositiveTimeBorchersSequence d) :
          BorchersSequence d).funcs n) =
          ((((F₁ - G₁) + (F₂ - G₂) : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n) := by
    intro n
    simp [sub_eq_add_neg]
    abel
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((F₁ + F₂) - (G₁ + G₂))
          ((F₁ + F₂) - (G₁ + G₂)) =
        PositiveTimeBorchersSequence.osInner OS ((F₁ - G₁) + (F₂ - G₂))
          ((F₁ - G₁) + (F₂ - G₂)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_add_left,
    PositiveTimeBorchersSequence.osInner_add_right,
    PositiveTimeBorchersSequence.osInner_add_right,
    h1_null, h12_null, h21_null, h2_null]
  simp

/-- Negation respects the OS null relation. -/
theorem neg_respects_equiv (F G : PositiveTimeBorchersSequence d)
    (h : osBorchersSetoid OS F G) :
    osBorchersSetoid OS (-F) (-G) := by
  show (PositiveTimeBorchersSequence.osInner OS ((-F) - (-G)) ((-F) - (-G))).re = 0
  have hfuncs :
      ∀ n,
        ((((-F) - (-G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          (((-(F - G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simp [sub_eq_add_neg]
    abel
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((-F) - (-G)) ((-F) - (-G)) =
        PositiveTimeBorchersSequence.osInner OS (-(F - G)) (-(F - G)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_neg_left,
    PositiveTimeBorchersSequence.osInner_neg_right, neg_neg]
  exact h

/-- Scalar multiplication respects the OS null relation. -/
theorem smul_respects_equiv (c : ℂ) (F G : PositiveTimeBorchersSequence d)
    (h : osBorchersSetoid OS F G) :
    osBorchersSetoid OS (c • F) (c • G) := by
  have hnull : PositiveTimeBorchersSequence.osInner OS (F - G) (F - G) = 0 :=
    PositiveTimeBorchersSequence.null_osInner_zero OS (F - G) (F - G) h
  show (PositiveTimeBorchersSequence.osInner OS ((c • F) - (c • G)) ((c • F) - (c • G))).re = 0
  have hfuncs :
      ∀ n,
        ((((c • F) - (c • G) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) =
          ((((c • (F - G)) : PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n) := by
    intro n
    simpa [BorchersSequence.sub_funcs, BorchersSequence.smul_funcs] using
      (smul_sub c ((F : BorchersSequence d).funcs n) ((G : BorchersSequence d).funcs n)).symm
  have hcongr :
      PositiveTimeBorchersSequence.osInner OS ((c • F) - (c • G)) ((c • F) - (c • G)) =
        PositiveTimeBorchersSequence.osInner OS (c • (F - G)) (c • (F - G)) := by
    unfold PositiveTimeBorchersSequence.osInner
    exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
      (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
  rw [hcongr, PositiveTimeBorchersSequence.osInner_smul_left,
    PositiveTimeBorchersSequence.osInner_smul_right, hnull]
  simp

instance instZero : Zero (OSPreHilbertSpace OS) where
  zero := Quotient.mk _ (0 : PositiveTimeBorchersSequence d)

instance instAdd : Add (OSPreHilbertSpace OS) where
  add := Quotient.map₂ (· + ·)
    (fun _ _ h₁ _ _ h₂ => add_respects_equiv OS _ _ _ _ h₁ h₂)

instance instNeg : Neg (OSPreHilbertSpace OS) where
  neg := Quotient.map (- ·) (fun _ _ h => neg_respects_equiv OS _ _ h)

instance instSMul : SMul ℂ (OSPreHilbertSpace OS) where
  smul c := Quotient.map (c • ·) (fun _ _ h => smul_respects_equiv OS c _ _ h)

instance instSub : Sub (OSPreHilbertSpace OS) where
  sub a b := a + (-b)

/-- If two positive-time sequences have identical components, their OS quotient
    classes are equal. -/
theorem mk_eq_of_funcs_eq (F G : PositiveTimeBorchersSequence d)
    (h : ∀ n, ((F : BorchersSequence d).funcs n) = ((G : BorchersSequence d).funcs n)) :
    (Quotient.mk (osBorchersSetoid OS) F : OSPreHilbertSpace OS) =
      Quotient.mk (osBorchersSetoid OS) G :=
  Quotient.sound (osBorchersSetoid_of_funcs_eq OS F G h)

instance instAddCommGroup : AddCommGroup (OSPreHilbertSpace OS) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        induction c using Quotient.inductionOn with
        | h H =>
          exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_assoc])
  zero_add a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  add_zero a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  add_comm a b := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_comm])
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℂ (OSPreHilbertSpace OS) where
  one_smul a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  mul_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [mul_smul])
  smul_zero c := by
    exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)
  smul_add c a b := by
    induction a using Quotient.inductionOn with
    | h F =>
      induction b using Quotient.inductionOn with
      | h G =>
        exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [smul_add])
  add_smul c₁ c₂ a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp [add_smul])
  zero_smul a := by
    induction a using Quotient.inductionOn with
    | h F =>
      exact mk_eq_of_funcs_eq OS _ _ (fun n => by simp)

instance instInner : Inner ℂ (OSPreHilbertSpace OS) where
  inner := OSPreHilbertSpace.innerProduct OS

@[simp] theorem inner_eq (F G : PositiveTimeBorchersSequence d) :
    @inner ℂ (OSPreHilbertSpace OS) (instInner OS) ⟦F⟧ ⟦G⟧ =
      PositiveTimeBorchersSequence.osInner OS F G := rfl

theorem inner_conj_symm (x y : OSPreHilbertSpace OS) :
    starRingEnd ℂ (@inner ℂ _ (instInner OS) y x) =
      @inner ℂ _ (instInner OS) x y := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      simpa using (PositiveTimeBorchersSequence.osInner_hermitian OS F G).symm

theorem inner_re_nonneg (x : OSPreHilbertSpace OS) :
    0 ≤ RCLike.re (@inner ℂ _ (instInner OS) x x) := by
  induction x using Quotient.inductionOn with
  | h F =>
    exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

theorem inner_add_left (x y z : OSPreHilbertSpace OS) :
    @inner ℂ _ (instInner OS) (x + y) z =
      @inner ℂ _ (instInner OS) x z + @inner ℂ _ (instInner OS) y z := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      induction z using Quotient.inductionOn with
      | h H =>
        exact PositiveTimeBorchersSequence.osInner_add_left OS F G H

theorem inner_smul_left (x y : OSPreHilbertSpace OS) (r : ℂ) :
    @inner ℂ _ (instInner OS) (r • x) y =
      starRingEnd ℂ r * @inner ℂ _ (instInner OS) x y := by
  induction x using Quotient.inductionOn with
  | h F =>
    induction y using Quotient.inductionOn with
    | h G =>
      exact PositiveTimeBorchersSequence.osInner_smul_left OS r F G

theorem inner_definite (x : OSPreHilbertSpace OS)
    (h : @inner ℂ _ (instInner OS) x x = 0) : x = 0 := by
  induction x using Quotient.inductionOn with
  | h F =>
    apply Quotient.sound
    show (PositiveTimeBorchersSequence.osInner OS (F - 0) (F - 0)).re = 0
    have hfuncs :
        ∀ n,
          (((F - (0 : PositiveTimeBorchersSequence d) : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n) =
            ((F : BorchersSequence d).funcs n) := by
      intro n
      simp
    have hcongr :
        PositiveTimeBorchersSequence.osInner OS (F - 0) (F - 0) =
          PositiveTimeBorchersSequence.osInner OS F F := by
      unfold PositiveTimeBorchersSequence.osInner
      exact (OSInnerProduct_congr_left d OS.S OS.E0_linear _ _ _ hfuncs).trans
        (OSInnerProduct_congr_right d OS.S OS.E0_linear _ _ _ hfuncs)
    have h' : PositiveTimeBorchersSequence.osInner OS F F = 0 := h
    rw [hcongr, h']
    simp

/-- The `InnerProductSpace.Core` instance on the honest Euclidean OS quotient. -/
instance instCore : InnerProductSpace.Core ℂ (OSPreHilbertSpace OS) where
  toCore := {
    toInner := instInner OS
    conj_inner_symm := inner_conj_symm OS
    re_inner_nonneg := inner_re_nonneg OS
    add_left := inner_add_left OS
    smul_left := inner_smul_left OS
  }
  definite := inner_definite OS

/-- The normed additive group structure induced by the honest OS inner product. -/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (OSPreHilbertSpace OS) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (instCore OS)

/-- The pre-Hilbert space structure on the honest Euclidean OS quotient. -/
noncomputable instance instInnerProductSpace :
    @InnerProductSpace ℂ (OSPreHilbertSpace OS) _
      (instNormedAddCommGroup OS).toSeminormedAddCommGroup :=
  @InnerProductSpace.ofCore ℂ _ _ _ _ (instCore OS).toCore

end OSPreHilbertSpace

/-- The zero-diagonal Wick-rotation relation between Wightman functions and their
    honest OS-I Euclidean counterparts.

    Formally: there exists a holomorphic function on the forward tube
    (the "analytic continuation") that:
    1. Has distributional boundary values equal to the Wightman functions W_n
    2. When restricted to Euclidean points (via Wick rotation) and paired with
       zero-diagonal test functions, reproduces the Euclidean family S_n on `°S`

    This is the honest Wightman -> OS-I surface.

    Ref: OS I (1973), Section 5; Streater-Wightman, Chapter 3 -/
def IsWickRotationPair {d : ℕ} [NeZero d]
    (S : SchwingerFunctions d) (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ (n : ℕ), ∃ (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
    -- F_analytic is holomorphic on the forward tube
    DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
    -- Boundary values of F_analytic = W_n (as distributions):
    -- For each test function f and approach direction η ∈ ForwardConeAbs,
    -- lim_{ε→0⁺} ∫ F_analytic(x + iε·η) f(x) dx = W_n(f)
    (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W n f))) ∧
    -- Euclidean restriction gives S_n on the zero-diagonal OS-I domain.
    (∀ (f : ZeroDiagonalSchwartz d n),
      S n f = ∫ x : NPointDomain d n,
        F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x))

-- `wightman_to_os` and `os_to_wightman` moved to Reconstruction/Main.lean
-- (proved via WickRotation.lean: wightman_to_os_full, os_to_wightman_full)

end
