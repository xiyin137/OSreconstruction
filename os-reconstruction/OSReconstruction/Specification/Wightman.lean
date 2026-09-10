/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.SpectralCondition
import OSReconstruction.Wightman.SchwartzTensorProduct









set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped SchwartzMap
open Topology
variable (d : ℕ) [NeZero d]

/-- The space of n copies of spacetime for n-point functions -/
abbrev NPointDomain (d n : ℕ) := Fin n → SpacetimeDim d

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPoint (d n : ℕ) := SchwartzMap (NPointDomain d n) ℂ

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

/-- Adjacent local commutativity condition for Wightman functions.

    For a collection of n-point functions W_n, local commutativity means:
    When adjacent points x_i and x_{i+1} are spacelike separated, swapping them
    in W_n doesn't change the value (for bosonic fields; fermionic fields get a
    sign).

    The precise condition is:
    W_n(..., x_i, x_{i+1}, ...) = W_n(..., x_{i+1}, x_i, ...)
    when (x_i - x_{i+1})² > 0 (spacelike separation in mostly positive
    signature).

    At the distribution level, this is expressed via test functions with
    spacelike-separated supports: if supp(f) and supp(g) are spacelike separated,
    then W₂(f ⊗ g) = W₂(g ⊗ f). -/
def IsAdjacentLocallyCommutativeWeak (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  -- For Schwartz functions f, g where g is the swap of adjacent coordinates
  -- i and i+1 in f, and the supports of f have spacelike-separated adjacent
  -- arguments, we have W_n(f) = W_n(g). Avoids constructing the swapped
  -- Schwartz function.
  ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : SchwartzNPoint d n),
    (∀ x : NPointDomain d n, f.toFun x ≠ 0 →
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
    (∀ x : NPointDomain d n,
      g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
    W n f = W n g

/-- Compatibility name for the standard adjacent-swap Wightman locality
predicate.  This is intentionally not an arbitrary non-adjacent pair-swap
property: moving a non-adjacent point through intervening fields requires the
corresponding chain of adjacent spacelike crossings. -/
abbrev IsLocallyCommutativeWeak :=
  IsAdjacentLocallyCommutativeWeak

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

/-- The inner product with explicit summation bounds. -/
def WightmanInnerProductN (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (F G : BorchersSequence d) (N₁ N₂ : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N₁,
    ∑ m ∈ Finset.range N₂,
      W (n + m) ((F.funcs n).conjTensorProduct (G.funcs m))

/-- Positive definiteness of Wightman functions -/
def Wightman.IsPositiveDefinite (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0

/-- Normalization: W_0 = 1 -/
def IsNormalized (W : (n : ℕ) → SchwartzNPoint d n → ℂ) : Prop :=
  ∀ f : SchwartzNPoint d 0, W 0 f = f 0

/-- The Wightman properties used before adding locality and clustering.
The full public reconstruction proves both additional properties for the
same literal `n`-point family on full Schwartz space. -/
structure WightmanFunctionsCore (d : ℕ) [NeZero d] where
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
  /-- One forward-tube kernel, with polynomial bounds on compact sets of
  imaginary parts and full-Schwartz distributional boundary recovery.
  This analytic condition does not by itself imply positive spectrum. -/
  spectrum_condition : ForwardTubeAnalyticityCompactSubset d W
  /-- Positive spectral support of the reduced tempered distributions. -/
  spectral_support : SpectralConditionDistribution d W
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

/-- A collection of public literal `n`-point Wightman functions satisfying the
    full reconstruction-side axioms.

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
  /-- One forward-tube kernel, with polynomial bounds on compact sets of
  imaginary parts and full-Schwartz distributional boundary recovery.
  This analytic condition does not by itself imply positive spectrum. -/
  spectrum_condition : ForwardTubeAnalyticityCompactSubset d W
  /-- Positive spectral support of the reduced tempered distributions. -/
  spectral_support : SpectralConditionDistribution d W
  /-- Adjacent local commutativity (weak form, the standard R3 surface). -/
  locally_commutative : IsAdjacentLocallyCommutativeWeak d W
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
  /-- Compact-height growth for the same kernel selected by
  `spectrum_condition`. This is a consequence of that kernel's package,
  not a second existential choice or a spectral-support assumption. -/
  spectrum_condition_compact_subset : ∀ (n : ℕ),
    ∀ (K : Set (Fin n → Fin (d + 1) → ℝ)), IsCompact K →
      (∀ y ∈ K, InForwardCone d n y) →
        ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
          ∀ (x y : Fin n → Fin (d + 1) → ℝ), y ∈ K →
            ‖(spectrum_condition n).choose
              (fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖ ≤
                C_bd * (1 + ‖x‖) ^ N :=
    fun n K hK hsub => (spectrum_condition n).choose_spec.2.1 K hK hsub

end
