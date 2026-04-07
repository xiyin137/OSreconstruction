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

set_option backward.isDefEq.respectTransparency false

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

/-- Lorentz covariance: W_n(Λx₁, ..., Λxₙ) = W_n(x₁, ..., xₙ) for all
    Λ in the connected Lorentz group SO⁺(1,d).

    For scalar fields, the Wightman functions are Lorentz invariant.
    For fields with spin s, there would be a transformation matrix D^{(s)}(Λ).

    At the distribution level: W_n(Λ⁻¹ · f) = W_n(f) where (Λ · f)(x) = f(Λ⁻¹x).

    We express this as invariance under the action of the Lorentz group on n-point
    configurations. -/
def IsLorentzCovariantWeak (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  -- For scalar fields: W_n is Lorentz invariant.
  -- For any connected Lorentz transformation Λ and Schwartz functions f, g
  -- such that g(x) = f(Λ⁻¹x₁,...,Λ⁻¹xₙ),
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

/-- For an arbitrary left Borchers vector, the Wightman inner product against a
concentrated right factor reduces to the single tensor term in each left
component. -/
theorem WightmanInnerProduct_right_single (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F : BorchersSequence d)
    {m : ℕ} (g : SchwartzNPoint d m) :
    WightmanInnerProduct d W F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        W (n + m) ((F.funcs n).conjTensorProduct g) := by
  unfold WightmanInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  rw [BorchersSequence.single_bound, Finset.sum_range_succ]
  have hright :
      ∑ j ∈ Finset.range m,
        W (n + j)
          ((F.funcs n).conjTensorProduct ((BorchersSequence.single m g).funcs j)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hj_ne : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
    rw [BorchersSequence.single_funcs_ne hj_ne,
      SchwartzMap.conjTensorProduct_zero_right, (hlin _).map_zero]
  rw [hright, zero_add, BorchersSequence.single_funcs_eq]

/-- The Wightman inner product against an arbitrary right Borchers vector is the
finite sum of its concentrated right components. -/
theorem WightmanInnerProduct_eq_sum_right_singles (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F G : BorchersSequence d) :
    WightmanInnerProduct d W F G =
      ∑ m ∈ Finset.range (G.bound + 1),
        WightmanInnerProduct d W F (BorchersSequence.single m (G.funcs m)) := by
  unfold WightmanInnerProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simpa [WightmanInnerProduct] using
    (WightmanInnerProduct_right_single (d := d) W hlin F (g := G.funcs m)).symm

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
def Wightman.IsPositiveDefinite (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0

-- Note: renamed from `IsPositiveDefinite` to avoid collision with
-- `Bochner.PositiveDefinite.IsPositiveDefinite` from the HilleYosida dependency.

/-- Normalization: W_0 = 1 -/
def IsNormalized (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ f : SchwartzNPoint d 0, W 0 f = f 0

/-! ### Wightman Functions Structure -/

/-- A collection of public literal `n`-point Wightman functions satisfying the
    reconstruction-side axioms.

    The field `W n` is the public literal `n`-point family on Schwartz test
    functions. Internal reduced-coordinate constructions later descend from
    these public `n`-point objects to reduced `(m + 1) -> m` data when needed,
    but that internal Route 1 bridge does not change the public meaning of
    `W n`. -/
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
  /-- Spectral-condition package used by the current reconstruction formalization.

      For the public literal `n`-point family `W n`, we currently package the
      analytic side as holomorphic continuation to the repo's `ForwardTube d n`
      together with distributional boundary-value recovery of `W n`.

      The important convention point is that `ForwardTube d n` is the current
      repo forward tube, which includes the extra basepoint condition
      `Im(z₀) ∈ V₊` in addition to the successive-difference conditions.
      Therefore this is slightly stronger than the minimal literal `n`-point
      tube often used in the standard literature.

      This field is the public absolute-coordinate input used by the
      reconstruction files. The internal Route 1 reduced layer later descends
      from the arity `m + 1` witness here to reduced arity `m` difference
      variables when building the reduced BHW bridge.

      Concretely we require:
      1. existence of an analytic continuation `W_analytic` on `ForwardTube d n`;
      2. holomorphicity on that current repo tube;
      3. distributional boundary values recovering the public literal
         `n`-point functional `W n`. -/
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
  positive_definite : Wightman.IsPositiveDefinite d W
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
  exact WightmanInnerProduct_hermitian_of Wfn.W Wfn.hermitian F G

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

/-- On a concentrated Borchers vector, `fieldOperatorAction` stays concentrated and
raises the degree by one by prepending the new test function. -/
theorem fieldOperatorAction_single_funcs (f : SchwartzSpacetime d)
    (n k : ℕ) (g : SchwartzNPoint d n) :
    (fieldOperatorAction f (BorchersSequence.single n g)).funcs k =
      (BorchersSequence.single (n + 1) (SchwartzMap.prependField f g)).funcs k := by
  cases k with
  | zero =>
      simp
  | succ k =>
      by_cases hk : k = n
      · subst hk
        simp
      · have hksucc : k.succ ≠ n + 1 := by
          omega
        simp [fieldOperatorAction_funcs_succ, BorchersSequence.single_funcs_ne hk,
          BorchersSequence.single_funcs_ne hksucc]

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

instance instContinuousAddZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousAdd (ZeroDiagonalSchwartz d n) := by
  delta ZeroDiagonalSchwartz
  infer_instance

instance instContinuousSMulZeroDiagonalSchwartz (d n : ℕ) :
    ContinuousSMul ℂ (ZeroDiagonalSchwartz d n) := by
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

/-- Euclidean spacetime translation preserves Lebesgue measure. -/
theorem translate_spacetime_measurePreserving (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (fun x : SpacetimeDim d => x + a) MeasureTheory.volume MeasureTheory.volume := by
  simpa [Pi.add_apply] using
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)) a)

/-- Componentwise Euclidean spacetime translation preserves Lebesgue measure on
`n`-point configuration space. -/
theorem translateNPoint_measurePreserving {n : ℕ} (a : SpacetimeDim d) :
    MeasureTheory.MeasurePreserving
      (fun x : NPointDomain d n => fun i : Fin n => x i + a)
      MeasureTheory.volume MeasureTheory.volume := by
  classical
  rw [show (fun x : NPointDomain d n => fun i : Fin n => x i + a) =
      (fun x : NPointDomain d n => fun i : Fin n => (fun y : SpacetimeDim d => y + a) (x i)) by
      rfl]
  exact MeasureTheory.volume_preserving_pi
    (fun _ : Fin n => translate_spacetime_measurePreserving (d := d) a)

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
