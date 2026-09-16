/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Adapted from the OSReconstruction specification and its mathematical definitions.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Reconstruction: definitions and statements for the standard Lean Comparator

This is the single mathematical reading file. It imports only Mathlib and gives
all project-specific definitions used by the three reconstruction propositions
at the end. Spatial dimension is `d > 0`; spacetime has dimension `d + 1`.

Read in order: spacetime and spectral conventions; Wightman axioms; the
zero-diagonal Euclidean test space and OS axioms; Wick pairing and growth;
the fixed reverse constructor; then the reconstruction statements.

Tensor products are specified by their pointwise values. The separate bridge
proofs establish that these witnesses exist and that the independent records
are equivalent to the production records, preserving the distribution families.
Standard Mathlib notions (Schwartz functions, integrals, derivatives, topologies,
linear maps, and finite sums) are imported in their usual library meanings.

`Challenge.lean` states the three propositions as named proof obligations.
`Solution.lean` proves them using the production library. Both import this
same file; the solution never imports the challenge's proof placeholders.
-/

/-! ## Spacetime, Fourier conventions, and Wightman axioms -/
noncomputable section
open MeasureTheory Complex Filter Set Topology Matrix
open scoped InnerProductSpace
namespace OSReconstructionAudit

abbrev Point (d : ℕ) := Fin (d + 1) → ℝ
abbrev Config (d n : ℕ) := Fin n → Point d
abbrev Test (d n : ℕ) := SchwartzMap (Config d n) ℂ
abbrev Family (d : ℕ) := (n : ℕ) → Test d n → ℂ

def metricSign (d : ℕ) (i : Fin (d + 1)) : ℝ := if i = 0 then -1 else 1

def quadratic (d : ℕ) (x : Point d) : ℝ :=
  ∑ i : Fin (d + 1), metricSign d i * x i * x i

def metric (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (metricSign d)

def ConnectedLorentz (d : ℕ) :=
  { L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ //
      Lᵀ * metric d * L = metric d ∧ L.det = 1 ∧ L 0 0 ≥ 1 }

def lorentzInverse {d : ℕ} (L : ConnectedLorentz d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  metric d * L.valᵀ * metric d

def openForwardCone (d : ℕ) (x : Point d) : Prop := x 0 > 0 ∧ quadratic d x < 0

def momentumCone (d : ℕ) : Set (Point d) := { x | quadratic d x ≤ 0 ∧ x 0 ≥ 0 }

def forwardDirections (d n : ℕ) (y : Config d n) : Prop :=
  ∀ k : Fin n,
    let previous : Point d := if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
    openForwardCone d (fun μ => y k μ - previous μ)

/-- The absolute-coordinate tube used by this formalization: in addition to
`Im (z_k - z_{k-1}) ∈ V₊` for `1 ≤ k < n`, it requires `Im z₀ ∈ V₊`.
For `n > 0` this is a proper subset of the usual literal n-point forward tube
defined only by the successive-difference conditions; `forwardAnalyticity` and
`wickPair` below use this smaller tube and do not assert extension to the larger
literal tube. -/
def forwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let previous : Fin (d + 1) → ℂ :=
      if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    openForwardCone d (fun μ => (z k μ - previous μ).im) }

def translationInvariant (d : ℕ) (W : Family d) : Prop :=
  ∀ (n : ℕ) (a : Point d) (f g : Test d n),
    (∀ x, g x = f (fun i => x i + a)) → W n f = W n g

def lorentzCovariant (d : ℕ) (W : Family d) : Prop :=
  ∀ (n : ℕ) (L : ConnectedLorentz d) (f g : Test d n),
    (∀ x, g x = f (fun i => Matrix.mulVec (lorentzInverse L) (x i))) → W n f = W n g

def adjacentLocality (d : ℕ) (W : Family d) : Prop :=
  ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (f g : Test d n),
    (∀ x, f x ≠ 0 → quadratic d (x i - x ⟨i.val + 1, hi⟩) > 0) →
    (∀ x, g x = f (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) → W n f = W n g

def uncurryCoordinates (d n : ℕ) : Config d n ≃ₗ[ℝ] (Fin n × Fin (d + 1) → ℝ) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  left_inv _ := rfl
  right_inv _ := funext fun ⟨_, _⟩ => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def euclideanCoordinates (d n : ℕ) :
    Config d n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin (d + 1)) :=
  (uncurryCoordinates d n).toContinuousLinearEquiv |>.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin (d + 1) => ℝ)).symm

/-- Mathlib's Fourier transform is exp(-2πi<x,p>) with the Euclidean inner product. -/
def fourier (d n : ℕ) (f : Test d n) : Test d n :=
  let e := euclideanCoordinates d n
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (SchwartzMap.fourierTransformCLM ℂ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f))

/-- The checked Fourier convention: negative sign, factor 2π, Euclidean pairing,
and Lebesgue volume on the Euclidean coordinate space. -/
theorem fourier_apply {d n : ℕ} (f : Test d n) (q : Config d n) :
    fourier d n f q =
      ∫ v : EuclideanSpace ℝ (Fin n × Fin (d + 1)),
        Complex.exp ((↑(-2 * Real.pi * ⟪v, euclideanCoordinates d n q⟫_ℝ) : ℂ) * Complex.I) *
          f ((euclideanCoordinates d n).symm v) := by
  change FourierTransform.fourier
    (fun v : EuclideanSpace ℝ (Fin n × Fin (d + 1)) => f ((euclideanCoordinates d n).symm v))
    (euclideanCoordinates d n q) = _
  rw [Real.fourier_eq']
  rfl

/-- The common-translation fiber integral, with x₀=a and xₖ=a+Σ_{j<k}ξⱼ. -/
def reduceBasepoint (d n : ℕ) (f : Test d (n + 1)) : Config d n → ℂ :=
  fun ξ => ∫ a : Point d, f (fun k μ => a μ + ∑ j : Fin k.val, ξ ⟨j.val, by omega⟩ μ)

/-- A relational Schwartz wrapper avoids concealing the fiber integral's formula. -/
def spectralSupport (d : ℕ) (W : Family d) : Prop :=
  ∀ n : ℕ, ∃ w : Test d n → ℂ,
    Continuous w ∧ IsLinearMap ℂ w ∧
    (∀ f : Test d (n + 1), ∃ g : Test d n,
      (∀ ξ, g ξ = reduceBasepoint d n f ξ) ∧ W (n + 1) f = w g) ∧
    (∀ φ : Test d n,
      (∀ q, φ q ≠ 0 → ∃ k : Fin n, q k ∉ momentumCone d) → w (fourier d n φ) = 0)

def forwardAnalyticity (d : ℕ) (W : Family d) : Prop :=
  ∀ n : ℕ, ∃ F : (Fin n → Fin (d + 1) → ℂ) → ℂ,
    DifferentiableOn ℂ F (forwardTube d n) ∧
    (∀ K : Set (Config d n), IsCompact K → K ⊆ { y | forwardDirections d n y } →
      ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ x y : Config d n, y ∈ K →
          ‖F (fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖ ≤ C * (1 + ‖x‖) ^ N) ∧
    (∀ (f : Test d n) (η : Config d n), forwardDirections d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Config d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))

/-- Euclidean time becomes imaginary Minkowski time. -/
def wickRotatePoint {d : ℕ} (x : Point d) : Fin (d + 1) → ℂ :=
  fun μ => if μ = 0 then Complex.I * (x 0 : ℂ) else (x μ : ℂ)

/-- External tensor product, specified by its values. -/
def tensorRelation {d n m : ℕ} (f : Test d n) (g : Test d m)
    (h : Test d (n + m)) : Prop :=
  ∀ x, h x = f (fun i => x (Fin.castAdd m i)) * g (fun j => x (Fin.natAdd n j))

/-- Borchers involution in the first factor: conjugation and argument reversal. -/
def conjugateTensorRelation {d n m : ℕ} (f : Test d n) (g : Test d m)
    (h : Test d (n + m)) : Prop :=
  ∀ x, h x =
    starRingEnd ℂ (f (fun i => x (Fin.castAdd m (Fin.rev i)))) *
      g (fun j => x (Fin.natAdd n j))

/-- A finitely supported sequence of Schwartz tests. -/
structure Borchers (d : ℕ) where
  funcs : (n : ℕ) → Test d n
  bound : ℕ
  bound_spec : ∀ n, bound < n → funcs n = 0

def positiveDefinite (d : ℕ) (W : Family d) : Prop :=
  ∀ (F : Borchers d) (H : (n m : ℕ) → Test d (n + m)),
    (∀ n m, conjugateTensorRelation (F.funcs n) (F.funcs m) (H n m)) →
    (∑ n ∈ Finset.range (F.bound + 1),
      ∑ m ∈ Finset.range (F.bound + 1), W (n + m) (H n m)).re ≥ 0

def clusterProperty (d : ℕ) (W : Family d) : Prop :=
  ∀ (n m : ℕ) (f : Test d n) (g : Test d m),
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : Point d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ∀ g_a : Test d m,
          (∀ x, g_a x = g (fun i => x i - a)) →
          ∀ h : Test d (n + m), tensorRelation f g_a h →
            ‖W (n + m) h - W n f * W m g‖ < ε

/-- The full literal n-point Wightman contract.
The redundant production field restating compact-height growth of the chosen
analytic kernel is already a consequence of `spectrum_condition`. -/
structure Wightman (d : ℕ) [NeZero d] where
  W : Family d
  linear : ∀ n, IsLinearMap ℂ (W n)
  tempered : ∀ n, Continuous (W n)
  normalized : ∀ f : Test d 0, W 0 f = f 0
  translation_invariant : translationInvariant d W
  lorentz_covariant : lorentzCovariant d W
  spectrum_condition : forwardAnalyticity d W
  spectral_support : spectralSupport d W
  locally_commutative : adjacentLocality d W
  positive_definite : positiveDefinite d W
  hermitian : ∀ (n : ℕ) (f g : Test d n),
    (∀ x, g x = starRingEnd ℂ (f (fun i => x (Fin.rev i)))) →
      W n g = starRingEnd ℂ (W n f)
  cluster : clusterProperty d W

end OSReconstructionAudit
end

/-! ## Zero-diagonal tests, OS axioms, and growth -/
-- Use Lean's default elaboration transparency. The former compatibility override
-- is unnecessary on Lean 4.33.0-rc1; the declarations below typecheck without it.
namespace OSReconstructionAudit
noncomputable section
open scoped SchwartzMap
open Topology

/-- Coincident configurations, including every pair of distinct labels. -/
def coincidenceLocus (d n : ℕ) : Set (Config d n) :=
  {x | ∃ i j : Fin n, i ≠ j ∧ x i = x j}

/-- All derivatives vanish on every coincidence diagonal. -/
def vanishesOnDiagonal {d n : ℕ} (f : Test d n) : Prop :=
  ∀ k : ℕ, ∀ x : Config d n, x ∈ coincidenceLocus d n →
    iteratedFDeriv ℝ k (f : Config d n → ℂ) x = 0

def zeroDiagonalSubmodule (d n : ℕ) : Submodule ℂ (Test d n) where
  carrier := {f | vanishesOnDiagonal f}
  zero_mem' := by
    intro k x hx
    by_cases hk : k = 0
    · subst hk
      ext m
      simp
    · change iteratedFDeriv ℝ k (fun _ : Config d n => (0 : ℂ)) x = 0
      exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) hk (0 : ℂ)) x
  add_mem' := by
    intro f g hf hg k x hx
    change iteratedFDeriv ℝ k
      ((f : Config d n → ℂ) + (g : Config d n → ℂ)) x = 0
    exact (iteratedFDeriv_add_apply
      ((f : Test d n).smooth _).contDiffAt
      ((g : Test d n).smooth _).contDiffAt).trans
      (by rw [hf k x hx, hg k x hx, zero_add])
  smul_mem' := by
    intro c f hf k x hx
    change iteratedFDeriv ℝ k (c • (f : Config d n → ℂ)) x = 0
    exact (iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c)
      (((f : Test d n).smooth _).contDiffAt)).trans
      (by rw [hf k x hx, smul_zero])

/-- The OS-I test space °S, with the subspace topology and linear operations. -/
def ZeroTest (d n : ℕ) := ↥(zeroDiagonalSubmodule d n)
instance (d n : ℕ) : AddCommMonoid (ZeroTest d n) := by
  delta ZeroTest; infer_instance
instance (d n : ℕ) : Module ℂ (ZeroTest d n) := by
  delta ZeroTest; infer_instance
instance (d n : ℕ) : TopologicalSpace (ZeroTest d n) := by
  delta ZeroTest; infer_instance

/-- Promote a Schwartz test to °S; use zero if it fails the diagonal condition.
This totalization is the one used in the production reflection-positive sum. -/
def ZeroTest.ofClassical {d n : ℕ} (f : Test d n) : ZeroTest d n := by
  classical
  by_cases h : vanishesOnDiagonal f
  · exact ⟨f, h⟩
  · exact 0

abbrev SchwingerFamily (d : ℕ) := (n : ℕ) → ZeroTest d n → ℂ

def timeReflection (d : ℕ) (x : Point d) : Point d :=
  fun i => if i = 0 then -x 0 else x i

def timeReflectionN (d : ℕ) {n : ℕ} (x : Config d n) : Config d n :=
  fun i => timeReflection d (x i)

def orderedPositiveTimeRegion (d n : ℕ) : Set (Config d n) :=
  {x | ∀ i : Fin n, 0 < x i 0 ∧ ∀ j : Fin n, i < j → x i 0 < x j 0}

/-- The tensor used in the OS sum, specified by its pointwise values. -/
def osTensorRelation {d n m : ℕ} (f : Test d n) (g : Test d m)
    (h : Test d (n + m)) : Prop :=
  ∀ x, h x = starRingEnd ℂ
    (f (fun i => timeReflection d (x (Fin.castAdd m i)))) *
    g (fun j => x (Fin.natAdd n j))

/-- The finite OS sum for an explicit family of reflected tensor witnesses. -/
def osInnerProduct {d : ℕ} (S : SchwingerFamily d) (F G : Borchers d)
    (H : (n m : ℕ) → Test d (n + m)) : ℂ :=
  ∑ n ∈ Finset.range (F.bound + 1),
    ∑ m ∈ Finset.range (G.bound + 1), S (n + m) (ZeroTest.ofClassical (H n m))

/-- The exact zero-diagonal OS axioms E0–E4. Tensor operations in E2 and E4
are given by their pointwise formula; neither factor is required to have positive arity.
The correspondence proofs supply these Schwartz witnesses and establish uniqueness,
so the universal witness formulation of E2 is not vacuous. -/
structure OS (d : ℕ) [NeZero d] where
  S : SchwingerFamily d
  E0_tempered : ∀ n, Continuous (S n)
  E0_linear : ∀ n, IsLinearMap ℂ (S n)
  E0_reality : ∀ (n : ℕ) (f g : ZeroTest d n),
    (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
    starRingEnd ℂ (S n f) = S n g
  E1_translation_invariant : ∀ (n : ℕ) (a : Point d) (f g : ZeroTest d n),
    (∀ x, g.1 x = f.1 (fun i => x i + a)) → S n f = S n g
  E1_rotation_invariant : ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
    R.transpose * R = 1 → R.det = 1 → ∀ (f g : ZeroTest d n),
    (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) → S n f = S n g
  E2_reflection_positive : ∀ (F : Borchers d),
    (∀ n, tsupport (F.funcs n : Config d n → ℂ) ⊆ orderedPositiveTimeRegion d n) →
    ∀ H : (n m : ℕ) → Test d (n + m),
      (∀ n m, osTensorRelation (F.funcs n) (F.funcs m) (H n m)) →
      (osInnerProduct S F F H).re ≥ 0
  E3_symmetric : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : ZeroTest d n),
    (∀ x, g.1 x = f.1 (fun i => x (σ i))) → S n f = S n g
  E4_cluster : ∀ (n m : ℕ) (f : ZeroTest d n) (g : ZeroTest d m),
    ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
      ∀ a : Point d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
        ∀ g_a : ZeroTest d m,
          (∀ x : Config d m, g_a.1 x = g.1 (fun i => x i - a)) →
          ∀ fg_a : ZeroTest d (n + m),
            (∀ x : Config d (n + m), fg_a.1 x =
              f.1 (fun i => x (Fin.castAdd m i)) *
              g_a.1 (fun j => x (Fin.natAdd n j))) →
            ‖S (n + m) fg_a - S n f * S m g‖ < ε

/-- All Schwartz seminorms with weight and derivative order at most n*s,
including (0,0) at arity zero. -/
def arityLinearSeminorm (d n s : ℕ) : Seminorm ℝ (Test d n) :=
  (Finset.Iic (n * s, n * s)).sup (schwartzSeminormFamily ℝ (Config d n) ℂ)

/-- The arity-linear version permits Sobolev order zero and bounds every arity. -/
structure arityLinearGrowth {d : ℕ} [NeZero d] (A : OS d) where
  normalized_zero : ∀ f : ZeroTest d 0, A.S 0 f = f.1 0
  sobolev_index : ℕ
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  growth_estimate : ∀ (n : ℕ) (f : ZeroTest d n),
    ‖A.S n f‖ ≤ alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
      arityLinearSeminorm d n sobolev_index f.1

/-- One common holomorphic kernel supplies both the full Schwartz boundary
values and all zero-diagonal Euclidean pairings. -/
def wickPair {d : ℕ} [NeZero d] (S : SchwingerFamily d) (W : Family d) : Prop :=
  ∀ n : ℕ, ∃ F : (Fin n → Fin (d + 1) → ℂ) → ℂ,
    DifferentiableOn ℂ F (forwardTube d n) ∧
    (∀ (f : Test d n) (η : Config d n), forwardDirections d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Config d n,
          F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f))) ∧
    (∀ f : ZeroTest d n, S n f = ∫ x : Config d n,
      F (fun k => wickRotatePoint (x k)) * f.1 x)

/-- Standard coordinate flattening, in the order fixed by finProdFinEquiv. -/
def uncurryLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  {(Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl}

def flattenLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (uncurryLinearEquiv n d 𝕜).trans (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

def flattenReal (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (flattenLinearEquiv n d ℝ).toContinuousLinearEquiv

/-- OS II (2.1): weighted coordinate derivatives through order r. -/
def coordinateWeight {m : ℕ} (x : Fin m → ℝ) : ℝ := Real.sqrt (1 + ∑ i, (x i) ^ 2)
def coordinateJet {m : ℕ} (r : ℕ) (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) (b : ℕ) (c : Fin b → Fin m) : ℝ :=
  coordinateWeight x ^ r * ‖iteratedFDeriv ℝ b f x (fun i => Pi.single (c i) 1)‖
def coordinateSeminormValues {m : ℕ} (r : ℕ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) : Set ℝ :=
  {v | ∃ (x : Fin m → ℝ) (b : ℕ), b ≤ r ∧ ∃ c : Fin b → Fin m,
    v = coordinateJet r f x b c}
def coordinateSeminorm {m : ℕ} (r : ℕ) (f : SchwartzMap (Fin m → ℝ) ℂ) : ℝ :=
  sSup (coordinateSeminormValues r f)
def originalSeminorm (d n r : ℕ) (f : Test d n) : ℝ :=
  coordinateSeminorm r
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenReal n (d + 1)).symm f)

/-- OS II (4.1): positive Sobolev order, scalar normalization, and a
factorial-only bound for positive arities. -/
structure originalGrowth {d : ℕ} [NeZero d] (A : OS d) where
  normalized_zero : ∀ f : ZeroTest d 0, A.S 0 f = f.1 0
  sobolev_index : ℕ
  sobolev_index_pos : 0 < sobolev_index
  alpha : ℝ
  gamma : ℝ
  alpha_pos : 0 < alpha
  growth_estimate : ∀ (n : ℕ), 0 < n → ∀ f : ZeroTest d n,
    ‖A.S n f‖ ≤ alpha * (n.factorial : ℝ) ^ gamma *
      originalSeminorm d n (n * sobolev_index) f.1

/-- OS II (4.3), retaining a positive output order and positive constants. -/
def outputGrowth (d : ℕ) (W : Family d) : Prop :=
  ∃ (w : ℕ) (A B : ℝ), 0 < w ∧ 0 < A ∧ 0 < B ∧
    ∀ (n : ℕ), 0 < n → ∀ f : Test d n,
      ‖W n f‖ ≤ A * B ^ (n ^ 2) * originalSeminorm d n (n * w) f

end
end OSReconstructionAudit

/-! ## The fixed reverse Schwinger constructor -/
namespace OSReconstructionAudit

/-- The complex proper Lorentz group: the complex metric-preserving matrices
of determinant one. No time-orientation inequality is imposed over ℂ. -/
structure ComplexLorentz (d : ℕ) where
  val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  metric_preserving : ∀ μ ν : Fin (d + 1),
    ∑ α : Fin (d + 1), (metricSign d α : ℂ) * val α μ * val α ν =
      if μ = ν then (metricSign d μ : ℂ) else 0
  proper : val.det = 1

/-- Permute the labels of a forward-tube configuration and then apply a
complex proper Lorentz transformation to every point. -/
def permutedExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ π : Equiv.Perm (Fin n),
    { z | ∃ (L : ComplexLorentz d) (w : Fin n → Fin (d + 1) → ℂ),
      (fun k => w (π k)) ∈ forwardTube d n ∧
      z = fun k μ => ∑ ν, L.val μ ν * w k ν }

/-- Allow one common complex translation to place the configuration in the
permuted extended tube. -/
def translatedPET (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∃ c : Fin (d + 1) → ℂ,
    (fun k μ => z k μ + c μ) ∈ permutedExtendedTube d n }

/-- A holomorphic extension of the selected forward-tube kernel. The production
bridge proves existence and uniqueness of its values on the extended tube. -/
def extensionProperty {d : ℕ} [NeZero d] (A : Wightman d) (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ) : Prop :=
  DifferentiableOn ℂ F (permutedExtendedTube d n) ∧
    ∀ z ∈ forwardTube d n, F z = (A.spectrum_condition n).choose z

/-- Select an extension by the explicit preceding predicate. The zero branch
only totalizes the definition; existence is proved from every Wightman record. -/
noncomputable def extendedKernel {d : ℕ} [NeZero d] (A : Wightman d) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ := by
  classical
  exact if h : ∃ F, extensionProperty A n F then h.choose else 0

/-- Evaluate the extension after choosing a common translation into the
permuted extended tube; set it to zero outside the translated domain. The
bridge proves independence of these choices on the relevant domain. -/
noncomputable def translatedKernel {d n : ℕ} [NeZero d] (A : Wightman d)
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ := by
  classical
  exact if hz : z ∈ translatedPET d n then
    extendedKernel A n (fun k μ => z k μ + hz.choose μ)
  else 0

/-- The fixed reverse constructor: Wick-rotate each Euclidean point, evaluate
the translated analytic extension, and integrate against the zero-diagonal test. -/
noncomputable def constructSchwinger {d : ℕ} [NeZero d] (A : Wightman d) : SchwingerFamily d :=
  fun n f => ∫ x : Config d n,
    translatedKernel A (fun k => wickRotatePoint (x k)) * f.1 x

end OSReconstructionAudit

/-! ## Reconstruction statements -/
namespace OSReconstructionAudit

/-- Qualitative E'-to-R: all Wightman axioms and the literal Wick pairing. -/
def EToR (d : ℕ) [NeZero d] : Prop :=
  ∀ A : OS d, arityLinearGrowth A →
    ∃ W : Wightman d, wickPair A.S W.W

/-- OS II E'-to-R': original-coordinate input and output bounds, with uniqueness
among all distribution families satisfying the same Wick pairing. -/
def EToROSII (d : ℕ) [NeZero d] : Prop :=
  ∀ A : OS d, originalGrowth A →
    ∃ W : Wightman d,
      wickPair A.S W.W ∧ outputGrowth d W.W ∧
      ∀ V : Family d, wickPair A.S V → V = W.W

/-- R-to-E with the fixed Schwinger constructor defined above. This direction
asserts all OS axioms and Wick pairing, without a Euclidean growth condition. -/
def RToE (d : ℕ) [NeZero d] : Prop :=
  ∀ W : Wightman d, ∃ A : OS d,
    A.S = constructSchwinger W ∧ wickPair A.S W.W

end OSReconstructionAudit
