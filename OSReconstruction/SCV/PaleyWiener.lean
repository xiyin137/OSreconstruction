/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.TubeDistributions
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Paley-Wiener-Schwartz Theorem

This file develops the Paley-Wiener-Schwartz theorem and its consequences for
holomorphic extension of distributions with one-sided Fourier support.

## Main results

* `paley_wiener_half_line` -- If T in S'(R) has supp(FT) in [0,infinity), then
  z -> T(e^{-iz.}) extends holomorphically to the upper half-plane.

* `paley_wiener_cone` -- Multi-dimensional generalization: if T in S'(R^m) has
  supp(FT) in C* (dual cone), then z -> T(e^{-iz.}) extends holomorphically
  to the tube domain T(C).

* `paley_wiener_converse` -- Converse: if F is holomorphic on T(C) with polynomial
  growth, then its distributional boundary value has Fourier transform supported in C*.

* `paley_wiener_one_step` -- Technical lemma for inductive analytic continuation:
  given a function on a tube whose distributional boundary value has one-sided
  Fourier support in one variable, extend holomorphicity by one variable.

## Mathematical Background

The classical Paley-Wiener theorem (for L^2) states that a function f in L^2(R) has
Fourier transform supported in [0,infinity) if and only if f extends holomorphically
to the upper half-plane with L^2 bounds on horizontal lines.

The Schwartz generalization replaces L^2 with tempered distributions S'(R^m) and
replaces L^2 bounds with polynomial growth. The key result: if T in S'(R^m) and
supp(FT) in C* (the dual cone of an open convex cone C in R^m), then the
Fourier-Laplace transform

    F(z) = <FT, e^{iz . .}>

is holomorphic on the tube domain T(C) = R^m + iC, with at most polynomial growth
as Im(z) approaches the boundary of C.

The converse also holds: any holomorphic function on T(C) with polynomial growth
is the Fourier-Laplace transform of a tempered distribution with Fourier support in C*.

## Application

The key consumer is `inductive_analytic_continuation` (OS II, Theorem 4.1) in
WickRotation.lean. At each induction step, one fixes all variables except one
spacetime component, obtains a function of one real variable with polynomial growth
(from E0') whose Fourier transform has one-sided support (from positivity of the
Hamiltonian / reflection positivity), and applies Paley-Wiener to extend
holomorphically to the upper half-plane in that variable.

## References

* Reed-Simon II, Theorem IX.16 (Paley-Wiener for L^2)
* Hormander, "The Analysis of Linear Partial Differential Operators I", Theorem 7.4.3
* Vladimirov, "Methods of the Theory of Generalized Functions", Section 25-26
* Streater-Wightman, "PCT, Spin and Statistics", Theorem 2-6
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

/-! ### Fourier support for tempered distributions

We formalize the notion of Fourier support for tempered distributions (continuous
linear functionals on Schwartz space). The Fourier transform of T in S'(R^m) is
defined by duality: (FT)(phi) = T(F(phi)) for phi in S(R^m).

We say supp(FT) subset S if T(F(phi)) = 0 whenever supp(phi) is disjoint from S.

Note: The Fourier transform on Schwartz space `SchwartzMap.fourierTransformCLM`
is available in Mathlib for inner product spaces. For `Fin m -> R` with the
standard Euclidean structure, this gives the m-dimensional Fourier transform.
However, to avoid type-class issues with `Fin m -> R` vs `EuclideanSpace R (Fin m)`,
we express Fourier support purely in terms of the distribution T and avoid
explicit use of the Fourier transform operator in the definitions.
-/

/-- A tempered distribution T (a continuous linear functional on Schwartz space)
    has **one-sided Fourier support** (in the half-line [0, infinity)) if
    T annihilates all Schwartz functions whose Fourier transform is supported
    in (-infinity, 0).

    Equivalently (by Fourier duality): for any test function phi whose support
    is contained in (-infinity, 0), the distributional pairing <FT, phi> = 0.

    We express this operationally: for any Schwartz function phi supported on
    the negative reals, the integral int F(x) * phi(x) dx = 0 (where F is
    the continuous function representing T near the boundary).

    This is the key hypothesis for the Paley-Wiener theorem. -/
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ)  : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ),
    (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
    T φ = 0

/-- A tempered distribution T on R^m has **Fourier support in a closed set S**
    if T annihilates all Schwartz functions whose support is disjoint from S.

    For the Paley-Wiener theorem, S will be the dual cone C*. -/
def HasFourierSupportIn {m : ℕ} (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (S : Set (Fin m → ℝ)) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
    (∀ x ∈ Function.support (φ : (Fin m → ℝ) → ℂ), x ∉ S) →
    T φ = 0

/-- The dual cone C* = { xi in R^m : <xi, y> >= 0 for all y in C }, where
    <.,.> is the standard Euclidean inner product (dot product).

    For an open convex cone C, the dual cone C* is a closed convex cone
    containing 0. The Paley-Wiener theorem states that tempered distributions
    with Fourier support in C* correspond to holomorphic functions on the
    tube domain T(C) with polynomial growth. -/
def dualCone {m : ℕ} (C : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  { ξ | ∀ y ∈ C, ∑ i : Fin m, ξ i * y i ≥ 0 }

/-- The dual cone is always closed. -/
theorem dualCone_isClosed {m : ℕ} (C : Set (Fin m → ℝ)) :
    IsClosed (dualCone C) := by
  have : dualCone C = ⋂ y ∈ C, { ξ : Fin m → ℝ | ∑ i, ξ i * y i ≥ 0 } := by
    ext ξ; simp [dualCone, mem_iInter]
  rw [this]
  apply isClosed_biInter
  intro y _hy
  exact isClosed_le continuous_const
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)

/-- The dual cone contains 0. -/
theorem zero_mem_dualCone {m : ℕ} (C : Set (Fin m → ℝ)) :
    (0 : Fin m → ℝ) ∈ dualCone C := by
  intro y _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, ge_iff_le, le_refl]

/-! ### Polynomial growth -/

/-- A holomorphic function on a tube domain has polynomial growth if for every
    compact K subset C, there exist C_K, N such that
    |F(x + iy)| <= C_K * (1 + |x|)^N for all x in R^m and y in K.

    This is the growth condition characterizing Fourier-Laplace transforms
    of tempered distributions (Vladimirov Section 25). -/
def HasPolynomialGrowthOnTube {m : ℕ} (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ (K : Set (Fin m → ℝ)), K ⊆ C → IsCompact K →
    ∃ (C_K : ℝ) (N : ℕ),
      0 < C_K ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => (x i : ℂ) + (y i : ℂ) * I)‖ ≤
          C_K * (1 + ‖x‖) ^ N

/-! ### Upper half-plane -/

/-- The upper half-plane { z in C : Im(z) > 0 }. -/
def upperHalfPlane : Set ℂ := { z : ℂ | z.im > 0 }

/-- A function on the real line with polynomial growth. -/
def HasPolynomialGrowthOnLine (f : ℝ → ℂ) : Prop :=
  ∃ (C_bound : ℝ) (N : ℕ), 0 < C_bound ∧
    ∀ x : ℝ, ‖f x‖ ≤ C_bound * (1 + |x|) ^ N

/-- The upper half-plane is open. -/
theorem upperHalfPlane_isOpen : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

/-! ### The Paley-Wiener-Schwartz theorem: 1D case -/

/-- **Paley-Wiener theorem for the half-line (1D).**

    If T in S'(R) is a continuous linear functional on Schwartz space with
    Fourier support in [0, infinity) (meaning: T(phi) = 0 whenever
    supp(phi) subset (-infinity, 0)), then the Fourier-Laplace transform
    z -> T(e^{-iz .}) extends holomorphically to the upper half-plane Im(z) > 0.

    More precisely, there exists a holomorphic function F on the upper half-plane
    such that for each Schwartz function phi, the smeared integral
    integral_R F(x + i*eta) * phi(x) dx converges to T(phi) as eta -> 0+.

    The proof (not yet formalized) proceeds by:
    1. Write T(phi) = (FT)(F^{-1}(phi)) by Parseval for distributions
    2. Since supp(FT) subset [0, infinity), the pairing localizes to xi >= 0
    3. For Im(z) > 0, the factor e^{-Im(z)*xi} provides exponential decay for xi >= 0
    4. This makes z -> T(e^{-iz .}) well-defined and holomorphic (differentiate under
       the distribution pairing)

    Sorry blocked by: Fourier-Laplace representation for tempered distributions,
    differentiation under the distribution pairing, and the connection between
    Fourier support and exponential decay.

    Ref: Reed-Simon II, Theorem IX.16; Hormander, Theorem 7.4.3 -/
theorem paley_wiener_half_line
    (T : SchwartzMap ℝ ℂ → ℂ)
    (hT_lin : IsLinearMap ℝ T) (hT_cont : Continuous T)
    (hT_supp : HasOneSidedFourierSupport T) :
    ∃ (F : ℂ → ℂ),
      DifferentiableOn ℂ F upperHalfPlane ∧
      -- F has polynomial growth on approach to the real axis
      (∀ (η : ℝ), 0 < η →
        HasPolynomialGrowthOnLine (fun x => F (x + η * I))) ∧
      -- Distributional boundary value: smeared integrals converge to T
      (∀ (φ : SchwartzMap ℝ ℂ),
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (T φ))) := by
  sorry

/-! ### The Paley-Wiener-Schwartz theorem: multi-dimensional case -/

/-- **Paley-Wiener theorem for cones (multi-dimensional).**

    If T in S'(R^m) has Fourier support in the dual cone C* of an open convex
    cone C subset R^m, then the Fourier-Laplace transform extends holomorphically
    to the tube domain T(C) = R^m + iC.

    This is the higher-dimensional generalization of `paley_wiener_half_line`.
    The proof strategy is similar: the dual cone support condition provides
    exponential decay in the Fourier representation when Im(z) in C, since
    sum_i Im(z_i) * xi_i > 0 for xi in C* \ {0} and Im(z) in C.

    Sorry blocked by: multi-dimensional Fourier-Laplace representation,
    exponential decay estimates from dual cone membership, and
    differentiation under the distribution pairing.

    Ref: Vladimirov, "Methods of Generalized Functions", Theorem 25.1;
    Hormander, "Analysis of PDE I", Theorem 7.4.3 -/
theorem paley_wiener_cone {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (hT_lin : IsLinearMap ℝ T) (hT_cont : Continuous T)
    (hT_supp : HasFourierSupportIn T (dualCone C)) :
    ∃ (F : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F (TubeDomain C) ∧
      HasPolynomialGrowthOnTube C F ∧
      -- Distributional boundary value recovers T
      (∀ (φ : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x)
        (nhdsWithin 0 (Ioi 0))
        (nhds (T φ))) := by
  sorry

/-! ### Converse Paley-Wiener: polynomial growth implies dual cone support -/

/-- **Converse Paley-Wiener theorem.**

    If F is holomorphic on the tube domain T(C) with polynomial growth, then its
    distributional boundary value T (which exists by `continuous_boundary_tube`)
    has Fourier transform supported in the dual cone C*.

    This is the converse direction of the Paley-Wiener correspondence:
      { T in S'(R^m) : supp(FT) subset C* }
        <--->
      { F holomorphic on T(C) with polynomial growth }

    The proof proceeds via the Fourier-Laplace representation: F is determined
    by its boundary value T, and the holomorphicity on T(C) forces FT to be
    supported where the Laplace integral converges, which is exactly C*.

    Sorry blocked by: Fourier inversion for distributions, uniqueness of
    Fourier-Laplace representation, and support characterization.

    Ref: Vladimirov, "Methods of Generalized Functions", Theorem 25.2;
    Hormander, "Analysis of PDE I", Theorem 7.4.2 -/
theorem paley_wiener_converse {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (F : (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hgrowth : HasPolynomialGrowthOnTube C F)
    (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (hT_lin : IsLinearMap ℝ T) (hT_cont : Continuous T)
    -- T is the distributional boundary value of F
    (h_bv : ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (T φ))) :
    HasFourierSupportIn T (dualCone C) := by
  sorry

/-! ### One-step extension: the key technical lemma for inductive continuation -/

/-- **One-step holomorphic extension via Paley-Wiener.**

    This is the key technical ingredient for `inductive_analytic_continuation`
    (OS II, Theorem 4.1). Given:

    1. A function F holomorphic on a tube T(C) in m complex variables.
    2. For each fixed z' (the other m-1 variables in T(C)), the function
       x_r -> F(z'_1, ..., x_r, ..., z'_m) has distributional boundary value
       in x_r whose Fourier transform is supported in [0, infinity).
    3. Polynomial growth in the r-th variable.

    Then F extends holomorphically to include the upper half-plane in the
    r-th variable: z_r with Im(z_r) > 0.

    The proof applies `paley_wiener_half_line` to the r-th variable (fixing the
    other variables as parameters), obtaining a holomorphic extension in z_r.
    Joint holomorphicity then follows from Osgood's lemma (separate holomorphicity
    in each variable implies joint holomorphicity for locally bounded functions).

    Physical interpretation: The one-sided Fourier support comes from the
    positivity of the Hamiltonian (spectral condition). The polynomial growth
    comes from the E0' linear growth condition. Together they allow extending
    analyticity from Euclidean to Minkowski one variable at a time.

    Sorry blocked by: `paley_wiener_half_line` (for each slice), Osgood's lemma
    for joint holomorphicity, and local boundedness of the parameterized extensions.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem paley_wiener_one_step {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    -- F is holomorphic on T(C) (m complex variables)
    (F : (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (TubeDomain C))
    -- The r-th variable has one-sided Fourier support
    (r : Fin m)
    -- For each fixed z' (the other m-1 variables in T(C)), the function
    -- x_r -> F(z'_1, ..., x_r, ..., z'_m) has distributional BV in x_r
    -- whose Fourier transform is supported in [0, infinity): test functions
    -- supported on (-inf, 0) integrate to 0 in the BV limit.
    (h_spectral : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      ∀ (φ : SchwartzMap ℝ ℂ),
        (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
        Tendsto (fun ε : ℝ =>
          ∫ t : ℝ, F (Function.update z' r (↑t + ↑ε * I)) * φ t)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0))
    -- Polynomial growth in the r-th variable
    (h_growth : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      HasPolynomialGrowthOnLine (fun t => F (Function.update z' r ↑t))) :
    -- Then F extends holomorphically to include Im(z_r) > 0
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      -- Holomorphic on the extended domain:
      -- original tube OR (other coordinates in tube AND r-th coordinate in upper half-plane)
      DifferentiableOn ℂ F_ext
        { z | (fun i => (z i).im) ∈ C ∨ (z r).im > 0 } ∧
      -- Agrees with F on original tube
      (∀ z ∈ TubeDomain C, F_ext z = F z) := by
  sorry

/-- **Simplified one-step extension for the inductive continuation (1D).**

    A cleaner version specialized to one complex variable: a continuous function
    on the real line with polynomial growth whose distributional Fourier transform
    is supported in [0, infinity) extends holomorphically to the upper half-plane.

    This formulation directly matches what `inductive_analytic_continuation`
    needs when all but one variable are fixed: extend holomorphicity in one
    coordinate from the real line to the upper half-plane.

    Sorry blocked by: `paley_wiener_half_line` (which it essentially restates
    for the special case where T is given by integration against a continuous function).

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem paley_wiener_one_step_simple
    (f : ℝ → ℂ) (hf_cont : Continuous f)
    -- Polynomial growth
    (hf_growth : HasPolynomialGrowthOnLine f)
    -- One-sided Fourier support: for test functions supported on (-inf, 0),
    -- the distributional pairing vanishes
    (h_spectral : ∀ (φ : SchwartzMap ℝ ℂ),
      (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
      ∫ t : ℝ, f t * φ t = 0) :
    ∃ (F_ext : ℂ → ℂ),
      DifferentiableOn ℂ F_ext upperHalfPlane ∧
      (∀ x : ℝ, F_ext ↑x = f x) ∧
      -- Polynomial growth on horizontal lines
      (∀ η : ℝ, 0 < η →
        HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * I))) := by
  sorry

/-! ### Uniqueness of Paley-Wiener extension -/

/-- The Paley-Wiener extension is unique: if two holomorphic functions on the
    upper half-plane have the same distributional boundary values on the real
    line, they agree.

    This follows from `distributional_uniqueness_tube` (in TubeDistributions.lean)
    applied to the cone (0, infinity) in R^1. The upper half-plane is the tube
    domain T((0,inf)) = { z : Im(z) > 0 }.

    Sorry blocked by: embedding the 1D case into the general tube domain
    framework and applying `distributional_uniqueness_tube`.

    Ref: Vladimirov, Section 26.3 -/
theorem paley_wiener_unique
    (F G : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hG : DifferentiableOn ℂ G upperHalfPlane)
    (hF_growth : ∀ η : ℝ, 0 < η →
      HasPolynomialGrowthOnLine (fun x => F (↑x + ↑η * I)))
    (hG_growth : ∀ η : ℝ, 0 < η →
      HasPolynomialGrowthOnLine (fun x => G (↑x + ↑η * I)))
    -- Same distributional boundary values
    (h_agree : ∀ (φ : SchwartzMap ℝ ℂ),
      Tendsto (fun η : ℝ => ∫ x : ℝ, (F (↑x + ↑η * I) - G (↑x + ↑η * I)) * φ x)
        (nhdsWithin 0 (Ioi 0))
        (nhds 0)) :
    ∀ z ∈ upperHalfPlane, F z = G z := by
  sorry

end SCV
