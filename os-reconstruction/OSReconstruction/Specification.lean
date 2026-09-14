/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIOriginalSeminorm

/-!
# Osterwalder-Schrader reconstruction specification

Read this file together with `Specification/Wightman.lean` for the input and
output records. Core supplies the Schwartz test-space and reflection operations;
no E-to-R or R-to-E reconstruction proof is imported here.

The final proposition definitions state the reconstruction targets without
claiming proofs. The actual public theorems are exported by
`Wightman/Reconstruction/Main.lean` and checked against this specification.
All dimensions below are positive spatial dimensions; spacetime has dimension d+1.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped SchwartzMap
open Topology
variable (d : ℕ) [NeZero d]

def OSInnerProduct (S : SchwingerFunctions d) (F G : BorchersSequence d) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1),
      S (n + m) (ZeroDiagonalSchwartz.ofClassical
        ((F.funcs n).osConjTensorProduct (G.funcs m)))

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

namespace OSReconstruction

/-- The OS-II source seminorm retains every weight/derivative pair through
the arity-linear bound, including `(0, 0)` at arity zero. -/
noncomputable def osArityLinearSchwartzSeminorm
    (d n s : Nat) : Seminorm Real (SchwartzNPoint d n) :=
  (Finset.Iic (n * s, n * s)).sup
    (schwartzSeminormFamily Real (NPointDomain d n) Complex)

/-- The genuine OS-II growth hypothesis on the original zero-diagonal
Euclidean test space. Its defining Schwartz orders grow linearly in arity;
the coefficient has the permitted exponential/factorial majorant. -/
structure OSArityLinearGrowthCondition
    (d : Nat) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  sobolev_index : Nat
  alpha : Real
  beta : Real
  gamma : Real
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  growth_estimate : ∀ (n : Nat) (f : ZeroDiagonalSchwartz d n),
    ‖OS.S n f‖ ≤ alpha * beta ^ n * (n.factorial : Real) ^ gamma *
      osArityLinearSchwartzSeminorm d n sobolev_index f.1

end OSReconstruction

/-- Public OS-II linear growth is the arity-linear condition. The former
fixed exact-index condition is not an equivalent reconstruction input. -/
abbrev OSLinearGrowthCondition (d : Nat) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :=
  OSReconstruction.OSArityLinearGrowthCondition d OS

/-- The honest zero-diagonal Schwinger family underlying an OS package.

    Public reconstruction theorems should be stated in terms of this actual
    Euclidean datum on `ZeroDiagonalSchwartz`. -/
def OsterwalderSchraderAxioms.schwinger {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) : SchwingerFunctions d :=
  OS.S

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

/-- Uncurrying `(Fin n → Fin d → 𝕜) ≃ₗ (Fin n × Fin d → 𝕜)`. -/
def uncurryLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  { (Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Concrete flattening `(Fin n → Fin d → 𝕜) ≃ₗ (Fin (n * d) → 𝕜)`.
    Composition of uncurrying with reindexing via `finProdFinEquiv`. -/
def flattenLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (uncurryLinearEquiv n d 𝕜).trans (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

/-- The flattening is a continuous linear equivalence over ℂ.
    Concrete: `f ↦ fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2`. -/
def flattenCLEquiv (n d : ℕ) :
    (Fin n → Fin d → ℂ) ≃L[ℂ] (Fin (n * d) → ℂ) :=
  (flattenLinearEquiv n d ℂ).toContinuousLinearEquiv

/-- The real version of the flattening. -/
def flattenCLEquivReal (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (flattenLinearEquiv n d ℝ).toContinuousLinearEquiv

namespace OSReconstruction

/-- The coordinate norm of OS II (2.1) on `n` spacetime points, in the
standard flattened order of the point and spacetime-coordinate labels. -/
def osiiOriginalNPointSeminorm (d n r : Nat) (f : SchwartzNPoint d n) : Real :=
  osiiOriginalSeminorm r
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (flattenCLEquivReal n (d + 1)).symm f)

/-- OS II E0', equation (4.1), in its original factorial-only coordinate-norm
convention. The positive order and the scalar normalization are explicit. -/
structure OSIIOriginalLinearGrowthCondition
    (d : Nat) [NeZero d] (OS : OsterwalderSchraderAxioms d) where
  normalized_zero : ∀ f : ZeroDiagonalSchwartz d 0, OS.S 0 f = f.1 0
  sobolev_index : Nat
  sobolev_index_pos : 0 < sobolev_index
  alpha : Real
  gamma : Real
  alpha_pos : 0 < alpha
  growth_estimate : ∀ (n : Nat), 0 < n -> ∀ f : ZeroDiagonalSchwartz d n,
    ‖OS.S n f‖ <= alpha * (n.factorial : Real) ^ gamma *
      osiiOriginalNPointSeminorm d n (n * sobolev_index) f.1

/-- R0' of OS II (4.3). This is extra information about a Wightman family,
not a new axiom required by the generic Wightman record. -/
def OSIIWightmanGrowthCondition (d : Nat)
    (W : (n : Nat) -> SchwartzNPoint d n -> Complex) : Prop :=
  ∃ (w : Nat) (A B : Real), 0 < w ∧ 0 < A ∧ 0 < B ∧
    ∀ (n : Nat), 0 < n -> ∀ f : SchwartzNPoint d n,
      ‖W n f‖ <= A * B ^ (n ^ 2) * osiiOriginalNPointSeminorm d n (n * w) f

/-- Qualitative E'-to-R, including the full Wightman record and Wick pairing. -/
def EToRStatement (d : Nat) [NeZero d] : Prop :=
  ∀ (OS : OsterwalderSchraderAxioms d), OSLinearGrowthCondition d OS →
    ∃ Wfn : WightmanFunctions d, IsWickRotationPair OS.schwinger Wfn.W

/-- Full OS II E'-to-R' with the original-coordinate input and output bounds. -/
def EToROSIIStatement (d : Nat) [NeZero d] : Prop :=
  ∀ (OS : OsterwalderSchraderAxioms d), OSIIOriginalLinearGrowthCondition d OS →
    ∃ Wfn : WightmanFunctions d,
      IsWickRotationPair OS.schwinger Wfn.W ∧
      OSIIWightmanGrowthCondition d Wfn.W ∧
      ∀ V : (n : Nat) → SchwartzNPoint d n → Complex,
        IsWickRotationPair OS.schwinger V → V = Wfn.W

/-- Full R-to-E, retaining equality with the specified Schwinger constructor.
The constructor is an argument to this proposition, not an extra hypothesis
in the reconstruction theorem. -/
def RToEStatement (d : Nat) [NeZero d]
    (reconstruct : WightmanFunctions d → SchwingerFunctions d) : Prop :=
  ∀ Wfn : WightmanFunctions d, ∃ OS : OsterwalderSchraderAxioms d,
    OS.S = reconstruct Wfn ∧ IsWickRotationPair OS.S Wfn.W

end OSReconstruction
end
