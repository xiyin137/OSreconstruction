# `schwartz_clm_fubini_exchange` Proof Blueprint

## Goal

Discharge the axiom in
[`OSReconstruction/GeneralResults/SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean):

```lean
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x)
```

Mathematically, this is the statement that a continuous linear functional on
Schwartz space commutes with a parameter integral of a Schwartz-valued family.
The only real work is constructing the Schwartz-valued integral in the
Fréchet topology.

## High-Level Route

Use bounded exhaustion and completeness of Schwartz space.

1. For each radius `R`, construct a bounded/truncated parameter
   integral
   ```lean
   Φ_R ξ = ∫ x in K_R, g x ξ * f x
   ```
   as a `SchwartzMap`.
2. Prove `Φ_R` is Cauchy in every Schwartz seminorm as `R → ∞`.
3. Use completeness of `SchwartzMap` to obtain `Φ`.
4. Identify `Φ ξ` with the scalar integral
   `∫ x, g x ξ * f x`.
5. Apply continuity and linearity of `T` to pass
   `T Φ_R → T Φ`, and identify the scalar limit with
   `∫ x, T (g x) * f x`.

This route avoids needing a direct Bochner integral into Schwartz space, which
is awkward because Schwartz space is locally convex/Fréchet rather than a
single normed space.

## Required Imports

Keep the proof in `GeneralResults/SchwartzFubini.lean` or split helper lemmas
into a new pure functional-analysis file, for example
`GeneralResults/SchwartzParamIntegral.lean`.

Likely useful imports:

```lean
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OSReconstruction.GeneralResults.DiffUnderIntegralSchwartz
```

The existing completeness result is currently in
`OSReconstruction/SCV/SchwartzComplete.lean`. Since this is pure Schwartz-space
infrastructure, the cleanest long-term move is to relocate that file or a small
dependency-free completeness interface into `GeneralResults`. If not moved,
importing it here is technically possible only if it does not create an import
cycle on the current branch.

## Phase 1: Scalar Integrability

First prove the scalar functions that appear in the statement are integrable.
Both lemmas should keep `hg_cont : Continuous g` in their hypotheses. The
polynomial seminorm bound controls size, but continuity supplies the
measurability needed by the scalar integrability lemmas.

Status: the Phase 1 helper lemmas below are now implemented and build in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:76).
The implementation also adds the required import:

```lean
import OSReconstruction.GeneralResults.DiffUnderIntegralSchwartz
```

### Pointwise Kernel Integrability

Implemented lemma:

```lean
lemma integrable_schwartz_fubini_pointwise {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ξ : Fin m → ℝ) :
    Integrable (fun x => g x ξ * f x)
```

Implementation notes:

- Use the existing pointwise estimate
  `SchwartzMap.norm_le_seminorm ℝ (g x) ξ` to bound
  `‖g x ξ‖` by `SchwartzMap.seminorm ℝ 0 0 (g x)`.
- Use `hg_bound 0 0` to get polynomial growth in `x`.
- Use `hg_cont`, composed with the continuous evaluation map
  ```lean
  ((BoundedContinuousFunction.evalCLM ℂ ξ).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin m → ℝ) ℂ)).continuous
  ```
  to get `AEStronglyMeasurable (fun x => g x ξ)`.
- Use rapid decay of `f` with an exponent larger than that polynomial.
- Call `integrable_polyGrowth_mul_schwartz` from
  [`DiffUnderIntegralSchwartz.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/DiffUnderIntegralSchwartz.lean).

### Functional Pairing Integrability

Implemented lemma:

```lean
lemma integrable_schwartz_fubini_clm_pairing {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable (fun x => T (g x) * f x)
```

Implemented support lemma:

```lean
lemma clm_polyGrowth_of_seminorm_polyGrowth {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, ‖T (g x)‖ ≤ C * (1 + ‖x‖) ^ N
```

Implementation notes:

- Bound `‖T ψ‖` by a finite supremum of Schwartz seminorms:
  `Seminorm.bound_of_continuous (schwartz_withSeminorms ...)`.
- Apply `hg_bound` to the finitely many seminorms and take the maximum
  polynomial exponent.
- Use `T.continuous.comp hg_cont` for measurability of `x ↦ T (g x)`.
- Finish with polynomial-growth times Schwartz-decay integrability.
- The support lemma uses the same finite-seminorm pattern as
  `seminorm_clm_family_poly_bound`; a later cleanup can refactor the shared
  finite-sup argument, but the code is already buildable as written.

## Phase 2: Bounded-Set Parameter Integral

Define bounded exhaustion sets. Cubes are usually easier than balls for
`Fin m → ℝ`:

```lean
def fubiniCube (m : ℕ) (R : ℕ) : Set (Fin m → ℝ) :=
  {x | ∀ i, ‖x i‖ ≤ (R : ℝ)}
```

Status: `fubiniCube` and its first structural lemmas now build in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:190):

```lean
def fubiniCube (m R : ℕ) : Set (Fin m → ℝ) :=
  {x | ∀ i, ‖x i‖ ≤ (R : ℝ)}

lemma isClosed_fubiniCube (m R : ℕ) :
    IsClosed (fubiniCube m R)

lemma measurableSet_fubiniCube (m R : ℕ) :
    MeasurableSet (fubiniCube m R)

lemma fubiniCube_mono (m : ℕ) {R S : ℕ} (hRS : R ≤ S) :
    fubiniCube m R ⊆ fubiniCube m S

lemma fubiniCube_subset_closedBall (m R : ℕ) :
    fubiniCube m R ⊆ Metric.closedBall (0 : Fin m → ℝ) (R : ℝ)

lemma isBounded_fubiniCube (m R : ℕ) :
    Bornology.IsBounded (fubiniCube m R)

lemma iUnion_fubiniCube_eq_univ (m : ℕ) :
    (⋃ R : ℕ, fubiniCube m R) = Set.univ

lemma integrableOn_iUnion_fubiniCube_of_integrable {m : ℕ}
    {F : (Fin m → ℝ) → ℂ} (hF : Integrable F) :
    IntegrableOn F (⋃ R : ℕ, fubiniCube m R) volume

lemma tendsto_integral_fubiniCube_of_integrable {m : ℕ}
    {F : (Fin m → ℝ) → ℂ} (hF : Integrable F) :
    Filter.Tendsto
      (fun R : ℕ => ∫ x in fubiniCube m R, F x)
      Filter.atTop
      (nhds (∫ x, F x))
```

The scalar exhaustion lemma is now available for both later limit passages:
pointwise identification of `Φ ξ` and the `T`-exchange limit. A separate
finite-measure cube lemma has not been needed yet; add it only if the bounded
set constructor requires it.

For `R : ℕ`, define:

```lean
Φ_R ξ = ∫ x in fubiniCube m R, g x ξ * f x
```

The most useful constructor is not compact-only. It should work for bounded
measurable parameter sets, because Phase 3 uses cube differences
`fubiniCube m S \ fubiniCube m R`, which are bounded and measurable but not
compact in the closed-set sense unless the difference is closed.

Target theorem:

```lean
theorem bounded_parameter_integral_schwartz_clm {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = ∫ x in K, g x ξ * f x) ∧
      T ΦK = ∫ x in K, T (g x) * f x
```

The compact version is then a corollary using
`hK_compact.isClosed.measurableSet` and compact boundedness.

Proof options:

- Preferred Lean route: use scalar differentiation under the integral for each
  iterated derivative, then package the result as a `SchwartzMap`.
- Practical sublemma: for every `k n`, prove a bound
  ```lean
  SchwartzMap.seminorm ℝ k n ΦK
    ≤ ∫ x in K, ‖f x‖ * SchwartzMap.seminorm ℝ k n (g x)
  ```
  or the same bound with a harmless finite constant.

On bounded `K`, use `hg_bound k n` and the boundedness of `K` to bound
`x ↦ SchwartzMap.seminorm ℝ k n (g x)` on `K`. Also use continuity of `f` and
boundedness of `K` to control `‖f x‖` on `K`, or more directly use scalar
integrability on `K`. Measurability comes from `hK_meas`.

The smooth dependence of `ΦK` on `ξ` requires differentiating under the
parameter integral. This is the compact/bounded-set analogue of the argument in
`hasDerivAt_schwartz_integral`: derivatives in `ξ` are dominated by the
corresponding Schwartz seminorm of `g x` times `‖f x‖`, and that dominator is
integrable on bounded `K`.

### Concrete Plan For The Next Implementation Step

Status: this first implementation step now builds in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:190).

Do not try to prove the whole bounded-set constructor in one Lean theorem.
First add the restriction lemmas and the scalar candidate. These are small
wrappers around Phase 1 and should build immediately.

```lean
lemma integrableOn_schwartz_fubini_pointwise {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ξ : Fin m → ℝ) :
    IntegrableOn (fun x => g x ξ * f x) K volume := by
  exact (integrable_schwartz_fubini_pointwise g f hg_cont hg_bound ξ).integrableOn

lemma integrableOn_schwartz_fubini_clm_pairing {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    IntegrableOn (fun x => T (g x) * f x) K volume := by
  exact (integrable_schwartz_fubini_clm_pairing T g f hg_cont hg_bound).integrableOn

noncomputable def boundedParamIntegralScalar {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → ℂ :=
  fun ξ => ∫ x in K, g x ξ * f x
```

After those wrappers build, split the constructor into two genuinely hard
pieces.

First, construct the Schwartz map:

```lean
theorem bounded_parameter_integral_scalar_is_schwartz {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ
```

Use the `SchwartzMap` structure constructor directly, but do not try to prove
smoothness from a scalar-looking formula. The values of `iteratedFDeriv` are
continuous multilinear maps, so introduce the derivative-family once and prove
that this family satisfies the recursive derivative relation.

The one useful new definition is now implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:219):

```lean
noncomputable def boundedParamIntegralDeriv {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) :
    (Fin m → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
  fun ξ =>
    ∫ x in K, f x • iteratedFDeriv ℝ n
      (fun η : Fin m → ℝ => g x η) ξ
```

The core proof has three moving parts:

1. `boundedParamIntegralDeriv K g f 0` is the zero-th iterated derivative of
   `boundedParamIntegralScalar K g f`. This is an extensional statement on
   `Fin 0` multilinear maps.
2. `boundedParamIntegralDeriv K g f n` has Fréchet derivative equal to the
   curried form of `boundedParamIntegralDeriv K g f (n + 1)`.
3. Therefore `iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f)` is
   `boundedParamIntegralDeriv K g f n`, by induction on `n`.

This is the refined theorem skeleton:

```lean
theorem bounded_parameter_integral_scalar_is_schwartz {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ := by
  let Φfun : (Fin m → ℝ) → ℂ := boundedParamIntegralScalar K g f
  let D :
      (n : ℕ) →
        (Fin m → ℝ) →
          ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    boundedParamIntegralDeriv K g f
  have h_iter :
      ∀ n ξ,
        iteratedFDeriv ℝ n Φfun ξ = D n ξ := by
    intro n ξ
    exact boundedParamIntegralScalar_iteratedFDeriv_eq
      K hK_meas hK_bdd g f hg_cont hg_bound n ξ
  have h_smooth : ContDiff ℝ ∞ Φfun := by
    exact boundedParamIntegralScalar_contDiff
      K hK_meas hK_bdd g f hg_cont hg_bound
  refine ⟨
    { toFun := Φfun
      smooth' := h_smooth
      decay' := ?_ }, ?_⟩
  · intro k n
    refine ⟨∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖, ?_⟩
    intro ξ
    rw [h_iter n ξ]
    calc
      ‖ξ‖ ^ k *
          ‖D n ξ‖
          ≤ ‖ξ‖ ^ k *
              ∫ x in K, ‖f x • iteratedFDeriv ℝ n
                (fun η : Fin m → ℝ => g x η) ξ‖ := by
            simp only [D, boundedParamIntegralDeriv]
            gcongr
            exact norm_integral_le_integral_norm _
      _ ≤ ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
            exact boundedParamIntegralScalar_decay_bound
              K hK_meas hK_bdd g f hg_cont hg_bound k n ξ
  · intro ξ
    rfl
```

The boundedness hypothesis `hK_bdd` may not be needed in the first version if
all domination is obtained from the global integrability helper below. Keep it
in the theorem statement because it is part of the bounded-set API and will be
used by later simple-function approximation arguments.

Only add the following helpers unless the implementation exposes a genuinely
missing API. Helpers 1 through 4 are now implemented; Helper 5 is the next
load-bearing step.

#### Helper 1: derivative evaluation is continuous on Schwartz space

Needed for measurability of
`x ↦ iteratedFDeriv ℝ n (fun η => g x η) ξ`.

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:270).

```lean
lemma continuous_schwartz_iteratedFDeriv_eval {m : ℕ}
    (n : ℕ) (ξ : Fin m → ℝ) :
    Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ =>
      iteratedFDeriv ℝ n (fun η : Fin m → ℝ => ψ η) ξ
```

Implemented proof route:

- Package `ψ ↦ iteratedFDeriv ℝ n (fun η => ψ η) ξ` as an ℝ-linear map into
  the normed space of continuous multilinear maps.
- Prove additivity and scalar compatibility using
  `iteratedFDeriv_add_apply` and `iteratedFDeriv_const_smul_apply`.
- Apply `WithSeminorms.continuous_normedSpace_rng` with the singleton Schwartz
  seminorm `{(0, n)}` and the bound
  `SchwartzMap.norm_iteratedFDeriv_le_seminorm`.

#### Helper 2: real polynomial growth times Schwartz norm is integrable

Needed because the seminorm-weight bounds are real-valued, while
`integrable_polyGrowth_mul_schwartz` is complex-valued.

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:219).

```lean
lemma integrable_polyGrowth_mul_schwartz_norm {m : ℕ}
    (a : (Fin m → ℝ) → ℝ)
    (ha_meas : AEStronglyMeasurable a volume)
    (ha_nonneg : ∀ x, 0 ≤ a x)
    (C : ℝ) (N : ℕ) (hC : 0 < C)
    (ha_growth : ∀ x, a x ≤ C * (1 + ‖x‖) ^ N)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Integrable (fun x => a x * ‖φ x‖) := by
  have hcomplex :
      Integrable (fun x => ((a x : ℂ) * φ x)) :=
    integrable_polyGrowth_mul_schwartz
      (g := fun x => (a x : ℂ))
      (hg_meas :=
        (Complex.measurable_ofReal.comp_aemeasurable
          ha_meas.aemeasurable).aestronglyMeasurable)
      (C := C) (N := N) hC ?_ φ
  · refine hcomplex.norm.congr ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [abs_of_nonneg (ha_nonneg x)]
  · intro x
    simpa [RCLike.norm_ofReal, abs_of_nonneg (ha_nonneg x)] using ha_growth x
```

This proof reuses the existing complex-valued integrability lemma by casting
`a x` to `ℂ`, then converts integrability of the complex norm back to the
real-valued function using `a x ≥ 0`.

#### Helper 3: seminorm-weight integrability

Needed for derivative-kernel integrability and the final decay bound.

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:240).

```lean
lemma integrable_schwartz_fubini_seminorm_weight {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (k n : ℕ) :
    Integrable fun x =>
      SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  obtain ⟨C, N, hC, hCbound⟩ := hg_bound k n
  exact integrable_polyGrowth_mul_schwartz_norm
    (a := fun x => SchwartzMap.seminorm ℝ k n (g x))
    (ha_meas :=
      (((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm (k, n)).comp
        hg_cont).aestronglyMeasurable)
    (ha_nonneg := fun x => apply_nonneg _ _)
    (C := C) (N := N) hC
    hCbound f
```

#### Helper 4: derivative kernels are integrable on bounded sets

Needed before applying `hasFDerivAt_integral_of_dominated_of_fderiv_le` with
the restricted measure `volume.restrict K`. State it for the
multilinear-map-valued kernel used by `boundedParamIntegralDeriv`.

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:322). The pointwise domination helper is
[`norm_boundedParamIntegralDeriv_kernel_le`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:305).

```lean
lemma integrableOn_boundedParamIntegral_iterated_deriv_kernel {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    IntegrableOn
      (fun x => f x • iteratedFDeriv ℝ n
        (fun η : Fin m → ℝ => g x η) ξ)
      K volume
```

Proof route:

- Strong measurability uses `continuous_schwartz_iteratedFDeriv_eval n ξ`
  composed with `hg_cont`, then multiplication by the continuous scalar
  function `x ↦ f x`.
- Dominate the norm by
  ```lean
  SchwartzMap.seminorm ℝ 0 n (g x) * ‖f x‖
  ```
  using `SchwartzMap.norm_iteratedFDeriv_le_seminorm`.
- Use `integrable_schwartz_fubini_seminorm_weight g f hg_cont hg_bound 0 n`
  and then restrict to `K`.

#### Helper 5: derivative formula for the derivative family

This is the load-bearing lemma for smoothness. The implemented version proves
the derivative-under-the-integral formula with the curried `(n + 1)`-st
kernel still inside the integral.

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:342).

```lean
lemma boundedParamIntegralDeriv_hasFDerivAt {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    HasFDerivAt
      (boundedParamIntegralDeriv K g f n)
      (∫ x in K,
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
          (f x • iteratedFDeriv ℝ (n + 1)
            (fun ζ : Fin m → ℝ => g x ζ) ξ))
      ξ
```

Proof route:

- Apply
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` to the restricted measure
  `volume.restrict K`.
- The integrand is
  ```lean
  fun ξ x => f x • iteratedFDeriv ℝ n
    (fun η : Fin m → ℝ => g x η) ξ
  ```
- The derivative in `ξ` is
  ```lean
  fun ξ x =>
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toContinuousLinearMap
      (f x • iteratedFDeriv ℝ (n + 1)
        (fun η : Fin m → ℝ => g x η) ξ)
  ```
- Use `fderiv_iteratedFDeriv` to identify the derivative of
  `iteratedFDeriv ℝ n (fun η => g x η)` with the curried `(n + 1)`-st
  derivative.
- The local derivative bound is pointwise and should be inline:
  ```lean
  ‖f x • iteratedFDeriv ℝ (n + 1) (fun η => g x η) η‖
    ≤ SchwartzMap.seminorm ℝ 0 (n + 1) (g x) * ‖f x‖
  ```
- Integrability of the bound is Helper 3.
The curry bridge is now implemented and building.

```lean
lemma boundedParamIntegralDeriv_hasFDerivAt_curry {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    HasFDerivAt
      (boundedParamIntegralDeriv K g f n)
      ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
        (boundedParamIntegralDeriv K g f (n + 1) ξ))
      ξ
```

It uses this standalone Bochner-integral commutation lemma for left-currying,
also implemented and building:

```lean
lemma integral_continuousMultilinearCurryLeft {m n : ℕ}
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (φ : α →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ)
    (hφ : Integrable φ μ) :
    (∫ a, (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
        (φ a) ∂μ)
      =
    (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
      (∫ a, φ a ∂μ)
```

Specialized use:

```lean
have hkernel_int :
    Integrable
      (fun x => f x • iteratedFDeriv ℝ (n + 1)
        (fun ζ : Fin m → ℝ => g x ζ) ξ)
      (volume.restrict K) :=
  (integrableOn_boundedParamIntegral_iterated_deriv_kernel
    K g f hg_cont hg_bound (n + 1) ξ).integrable

have hcurry_integral :
    (∫ x in K,
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
        (f x • iteratedFDeriv ℝ (n + 1)
          (fun ζ : Fin m → ℝ => g x ζ) ξ))
      =
    (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
      (boundedParamIntegralDeriv K g f (n + 1) ξ) := by
  simpa [boundedParamIntegralDeriv] using
    integral_continuousMultilinearCurryLeft
      (μ := volume.restrict K)
      (φ := fun x => f x • iteratedFDeriv ℝ (n + 1)
        (fun ζ : Fin m → ℝ => g x ζ) ξ)
      hkernel_int
```

Implemented proof of the blocker theorem:

```lean
  letI :
      NormedAddCommGroup
        ((Fin m → ℝ) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let e :=
    continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ
  have hcurried : Integrable (fun a => e (φ a)) μ :=
    hφ.congr'
      (e.continuous.comp_aestronglyMeasurable hφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun a => by simp [e])
  ext v tail
  change ((∫ a, e (φ a) ∂μ) v) tail = ((e (∫ a, φ a ∂μ)) v) tail
  have hcurried_v : Integrable (fun a => (e (φ a)) v) μ :=
    hcurried.apply_continuousLinearMap v
  rw [ContinuousLinearMap.integral_apply hcurried v]
  rw [ContinuousMultilinearMap.integral_apply hcurried_v tail]
  change (∫ x, φ x (Fin.cons v tail) ∂μ) =
    (∫ a, φ a ∂μ) (Fin.cons v tail)
  rw [ContinuousMultilinearMap.integral_apply hφ (Fin.cons v tail)]
```

Notes from the implementation:

Direct attempts using `ContinuousLinearMap.integral_comp_comm` and
`LinearIsometry.integral_comp_comm` hit an instance mismatch between the
`ContinuousMultilinearMap.seminormedAddCommGroup` structure used by the curry
equivalence and the `NormedAddCommGroup` structure expected by those integral
theorems. Adding
`Mathlib.Analysis.Normed.Operator.NormedSpace` fixes a missing normed instance
elsewhere, but does not by itself make the direct `integral_comp_comm` proof
elaborate for the curry equivalence. The working proof avoids this by:

- adding a local `NormedAddCommGroup` instance for the curried continuous-linear
  map target;
- proving curried integrability using `Integrable.congr'` and norm preservation
  rather than `LinearIsometryEquiv.integrable_comp_iff`, which timed out;
- proving the equality extensionally with scalar-valued `integral_apply`
  lemmas.

#### Helper 6: identify actual iterated derivatives

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:506).
This is a separate helper because it keeps the `SchwartzMap` constructor proof
readable.

```lean
lemma boundedParamIntegralScalar_iteratedFDeriv_eq {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∀ n ξ,
      iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) ξ =
        boundedParamIntegralDeriv K g f n ξ
```

Implemented proof route:

- Base case: ext over `Fin 0`; expose `boundedParamIntegralDeriv` and
  `boundedParamIntegralScalar`; use
  `ContinuousMultilinearMap.integral_apply` to push evaluation through the
  Bochner integral; finish with `iteratedFDeriv_zero_apply` and `mul_comm`.
- Step case: rewrite `iteratedFDeriv_succ_eq_comp_left`; use the induction
  hypothesis as a function equality; use Helper 5 to identify
  `fderiv (boundedParamIntegralDeriv K g f n)`.
- The final coercion between the derivative and the `(n + 1)` multilinear map
  is handled by `continuousMultilinearCurryLeftEquiv`.

#### Helper 7: smoothness and decay wrappers

Status: implemented and building in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:551).
These are thin wrappers around Helpers 5 and 6, added to keep the constructor
proof readable.

```lean
lemma boundedParamIntegralScalar_contDiff {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ContDiff ℝ (⊤ : ℕ∞) (boundedParamIntegralScalar K g f)
```

Implemented proof route:

- Use `contDiff_of_differentiable_iteratedFDeriv`.
- Rewrite `iteratedFDeriv` using Helper 6.
- Differentiability of `boundedParamIntegralDeriv K g f n` follows from
  Helper 5 pointwise.

```lean

lemma boundedParamIntegralScalar_decay_bound {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (k n : ℕ) (ξ : Fin m → ℝ) :
    ‖ξ‖ ^ k *
        ‖∫ x in K, f x • iteratedFDeriv ℝ n
          (fun η : Fin m → ℝ => g x η) ξ‖
      ≤ ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖
```

Implemented proof route:

- Use `norm_integral_le_integral_norm` for the Bochner integral over
  `volume.restrict K`.
- Pull out the fixed factor `‖ξ‖ ^ k` with `integral_const_mul`.
- Compare integrands using `SchwartzMap.le_seminorm ℝ k n`.
- Use `integrable_schwartz_fubini_seminorm_weight` restricted to `K` for the
  real bound.

The bounded-set Schwartz constructor is also implemented and building:

```lean
theorem bounded_parameter_integral_scalar_is_schwartz {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ
```

It uses `boundedParamIntegralScalar_contDiff` for `smooth'`, and for `decay'`
rewrites the actual iterated derivative using Helper 6 before applying
`boundedParamIntegralScalar_decay_bound`.

Second, prove the `T` exchange as part of the same construction pipeline, not
from pointwise equality alone:

```lean
theorem bounded_parameter_integral_schwartz_clm_exchange {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x
```

The key warning is that a theorem of the form
`hΦK : ∀ ξ, ΦK ξ = ∫ x in K, g x ξ * f x → T ΦK = ...` is too weak as a
standalone proof strategy. The equality after applying an arbitrary continuous
linear functional should be justified by the approximation or limiting process
used to construct `ΦK`: approximate `x ↦ f x • g x` by simple functions in the
Schwartz topology on `K`, apply `T` to the finite sums, then pass to the scalar
integral using `integrableOn_schwartz_fubini_clm_pairing`.

Once `bounded_parameter_integral_schwartz_clm_exchange` exists, the original
`bounded_parameter_integral_schwartz_clm` theorem is just this theorem with
`boundedParamIntegralScalar` unfolded.

The first helper for this target is implemented and building:

```lean
lemma clm_norm_le_finite_schwartz_seminorms {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖T ψ‖ ≤
          C * (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ
```

It is the finite-seminorm continuity bound for a fixed `T`, extracted directly
from `Seminorm.bound_of_continuous`. This is the quantitative estimate needed
to pass from convergence in finitely many Schwartz seminorms to convergence
after applying `T`.

The corresponding finite-envelope integrability helper is also implemented and
building:

```lean
lemma integrable_schwartz_fubini_finset_sum_seminorm_weight {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x =>
      (∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (g x)) * ‖f x‖
```

This packages the domination needed after `T` has been reduced to finitely many
seminorms. It deliberately uses the finite sum rather than the finite supremum,
because `Seminorm.finset_sup_le_sum` gives the needed domination and the sum is
straightforwardly integrable from the single-seminorm weight lemma.

The next implemented support layer is the complex-seminorm version needed by
the complex-linear functional `T`, plus the pointwise domination for weighted
kernels:

```lean
lemma clm_norm_le_finite_schwartz_seminorms_complex {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖T ψ‖ ≤
          C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ

lemma schwartz_seminorm_complex_eq_real {m : ℕ}
    (k n : ℕ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap.seminorm ℂ k n ψ = SchwartzMap.seminorm ℝ k n ψ

lemma integrable_schwartz_fubini_finset_sum_seminorm_weight_complex {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x =>
      (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (g x)) * ‖f x‖

lemma clm_weighted_kernel_norm_le_finset_sum {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ)) (C : ℝ) (hC_nonneg : 0 ≤ C)
    (hT : ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      ‖T ψ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    ‖T (f x • g x)‖ ≤
      C * ((∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (g x)) * ‖f x‖)

lemma integrable_schwartz_fubini_clm_weighted_kernel {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x => T (f x • g x)

lemma integrableOn_schwartz_fubini_clm_weighted_kernel {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    IntegrableOn (fun x => T (f x • g x)) K volume
```

This is deliberately only a domination result, not the exchange theorem itself.
It is the estimate needed when the simple-function approximants for
`x ↦ f x • g x` are pushed through `T`. The two integrability wrappers package
the resulting measurable domination so the exchange proof can focus on the
approximation/limit step.

The finite-simple algebraic base of the exchange argument is also implemented:

```lean
lemma clm_finset_weighted_sum_exchange {m : ℕ} {ι : Type*}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (s : Finset ι)
    (c : ι → ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ) :
    T (∑ i ∈ s, c i • ψ i) = ∑ i ∈ s, c i * T (ψ i)

lemma clm_weighted_kernel_apply {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    T (f x • g x) = T (g x) * f x

lemma integral_clm_weighted_kernel_eq_pairing {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    ∫ x in K, T (f x • g x) = ∫ x in K, T (g x) * f x

lemma clm_exchange_of_tendsto_approximants {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (Φ : SchwartzMap (Fin m → ℝ) ℂ)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (I : ℕ → ℂ)
    (J : ℂ)
    (hΦn : Filter.Tendsto Φn Filter.atTop (nhds Φ))
    (hI : Filter.Tendsto I Filter.atTop (nhds J))
    (hstep : ∀ n, T (Φn n) = I n) :
    T Φ = J

lemma tendsto_schwartz_atTop_iff_seminorm {m : ℕ}
    {u : ℕ → SchwartzMap (Fin m → ℝ) ℂ}
    {Φ : SchwartzMap (Fin m → ℝ) ℂ} :
    Filter.Tendsto u Filter.atTop (nhds Φ) ↔
      ∀ k n ε, 0 < ε →
        ∃ N, ∀ N' ≥ N,
          SchwartzMap.seminorm ℝ k n (u N' - Φ) < ε

lemma tendsto_schwartz_atTop_of_tendsto_seminorm {m : ℕ}
    {u : ℕ → SchwartzMap (Fin m → ℝ) ℂ}
    {Φ : SchwartzMap (Fin m → ℝ) ℂ}
    (h : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n (u N - Φ))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds Φ)
```

These lemmas discharge the exact finite-sum case and normalize the scalar target
integral. The remaining bounded-set exchange work is therefore purely the
approximation statement: construct approximants converging to the bounded
Schwartz-valued integral in the Schwartz topology and show their scalar
`T`-images converge to the set integral. The limit bridge packages the final
use of `T.continuous` and `tendsto_nhds_unique`.

The topology convergence criteria reduce that approximation statement to
real-valued seminorm estimates. The next proof should therefore avoid talking
about generic topological convergence until the last line: prove
`SchwartzMap.seminorm ℝ k n (Φ_N - ΦK) → 0` for every `(k,n)`, then invoke
`tendsto_schwartz_atTop_of_tendsto_seminorm`.

### Blocker Plan: Bounded-Set Approximants

The current blocker is the absence of a concrete approximation theorem for the
Schwartz-valued bounded integral. Do not try to prove
`bounded_parameter_integral_schwartz_clm_exchange` directly. Prove the following
local package first.

Use a simple-function approximation of the **Schwartz-valued kernel**

```lean
F : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ
F x := f x • g x
```

with measure `μ := volume.restrict K`. Because `SchwartzMap` is not a normed
Bochner target in this development, the approximants should be tracked through
their seminorm integrals, not through a generic Bochner integral in
`SchwartzMap`.

Recommended local definitions:

```lean
def boundedKernel {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ :=
  fun x => f x • g x

noncomputable def boundedKernelApprox
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (N : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  -- finite sum over the range of a simple approximation to `boundedKernel g f`
  -- each term is `(μ (preimage cell)).toReal • sampledSchwartzValue`
```

There are two possible implementation routes:

1. **Preferred if Lean instances are available**: use `SimpleFunc.approxOn` for
   `boundedKernel g f`. This requires checking that `SchwartzMap` has enough
   pseudo-emetric/borel/separable-range structure for the API. Earlier
   inspection showed the usual normed `Bochner` approximation API does not
   directly apply to `SchwartzMap`, but pointwise simple approximation may still
   be usable if the needed measurable-space and separability instances resolve.
2. **Fallback, more manual but robust**: state an approximation lemma in terms
   of finite partitions and sampled values. The theorem should assume the
   finite approximants satisfy the seminorm convergence estimates. This is
   enough to prove the exchange theorem and leaves only a standard measure
   approximation result as a later isolated lemma.

The immediate theorem to prove should be the fallback interface:

```lean
theorem bounded_parameter_integral_schwartz_clm_exchange_of_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (In : ℕ → ℂ)
    (hΦn :
      ∀ k n,
        Filter.Tendsto
          (fun N => SchwartzMap.seminorm ℝ k n
            (Φn N - Classical.choose
              (bounded_parameter_integral_scalar_is_schwartz
                K hK_meas hK_bdd g f hg_cont hg_bound)))
          Filter.atTop (nhds 0))
    (hIn :
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))))
    (hstep : ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x
```

This fallback interface is now implemented in Lean, along with two wrappers:

```lean
theorem bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants {m : ℕ}
    ...

theorem bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants {m : ℕ}
    ...
```

These theorems prove the bounded-set exchange once the approximating sequence
and its scalar convergence are supplied. They do **not** prove the unconditional
bounded-set exchange; the only missing input is the existence/convergence of the
approximants below.

One required measure-theory prerequisite for the remaining approximation
argument is also implemented:

```lean
lemma isFiniteMeasure_restrict_of_isBounded {m : ℕ}
    (K : Set (Fin m → ℝ)) (hK_bdd : Bornology.IsBounded K) :
    IsFiniteMeasure (volume.restrict K)
```

This allows the eventual simple/L1 approximation argument to work over the
finite measure space `volume.restrict K`.

Proof outline for this fallback theorem:

1. Let `ΦK := Classical.choose (bounded_parameter_integral_scalar_is_schwartz ...)`.
2. Get the pointwise identity from the `choose_spec`.
3. Convert `hΦn` to `Filter.Tendsto Φn atTop (nhds ΦK)` using
   `tendsto_schwartz_atTop_of_tendsto_seminorm`.
4. Use `clm_exchange_of_tendsto_approximants` with
   `J := ∫ x in K, T (f x • g x)`.
5. Rewrite the target integral using `integral_clm_weighted_kernel_eq_pairing`.

After that fallback theorem compiles, prove the actual approximation hypotheses:

```lean
theorem exists_bounded_kernel_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    ...
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
      (∀ k n, Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n (Φn N - ΦK))
        Filter.atTop (nhds 0)) ∧
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))) ∧
      ∀ N, T (Φn N) = In N
```

The seminorm convergence estimate should be proved from the already available
bounded-integral derivative/seminorm machinery. For each `(k,n)`, reduce the
seminorm of the approximant error to an integral of the pointwise seminorm error
of the kernel:

```lean
SchwartzMap.seminorm ℝ k n (Φn N - ΦK)
  ≤ ∫ x in K,
      SchwartzMap.seminorm ℝ k n (simpleApprox N x - boundedKernel g f x)
```

Then prove the right side tends to zero by scalar dominated convergence or a
simple-function L1 approximation theorem applied to the seminormed scalar
functions. The domination is supplied by the finite-seminorm growth lemmas
already proved:

```lean
integrable_schwartz_fubini_seminorm_weight
integrable_schwartz_fubini_finset_sum_seminorm_weight
integrable_schwartz_fubini_clm_weighted_kernel
```

Key warning: proving the seminorm convergence only pointwise in `ξ` is not
enough. The proof must control the full Schwartz seminorm `(k,n)`, including
all derivatives and the polynomial weight. That is why the final convergence
goal is written with `SchwartzMap.seminorm`, not with evaluation functionals.

### Real Blocker: L1 Approximation In Schwartz Seminorms

The real blocker is **not** the continuous-linear-map exchange anymore. That
part is already reduced to `clm_exchange_of_tendsto_approximants`. The real
missing theorem is an approximation theorem for the map

```lean
x ↦ f x • g x : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ
```

on the finite measure space `volume.restrict K`, where convergence is measured
by each Schwartz seminorm. In Lean form, the missing theorem should look like:

```lean
theorem exists_bounded_kernel_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
      (∀ k n,
        Filter.Tendsto
          (fun N => SchwartzMap.seminorm ℝ k n
            (Φn N -
              Classical.choose
                (bounded_parameter_integral_scalar_is_schwartz
                  K hK_meas hK_bdd g f hg_cont hg_bound)))
          Filter.atTop (nhds 0)) ∧
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))) ∧
      ∀ N, T (Φn N) = In N
```

Why this is not automatic:

- `SchwartzMap` currently has its topology from `WithSeminorms`; it is complete
  and first-countable, but it is not being used as a normed Bochner target.
- Mathlib's convenient `SimpleFunc.approxOn`/Bochner `L1` approximation theorems
  require metric/emetric and borel/separable-range structure on the target in a
  way that does not immediately resolve for `SchwartzMap`.
- Pointwise approximation of evaluations `x ↦ f x * g x ξ` is too weak. The
  theorem needs convergence in every seminorm
  `SchwartzMap.seminorm ℝ k n`, including derivatives in `ξ` and polynomial
  weights.

The proof strategy should therefore avoid a generic Bochner integral into
`SchwartzMap`. Work seminorm-by-seminorm.

Detailed strategy:

1. For each finite set of seminorm indices `s : Finset (ℕ × ℕ)`, define a scalar
   control seminorm on the target:

   ```lean
   p_s ψ := (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ
   ```

   Prove the kernel is integrable in this seminorm:

   ```lean
   Integrable fun x =>
     (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (f x • g x)
   ```

   Reduce this to the already-proved finite-sum bound and
   `integrable_schwartz_fubini_finset_sum_seminorm_weight`.

2. Prove a finite-seminorm simple approximation lemma:

   ```lean
   lemma exists_simple_approx_finite_schwartz_seminorm
       (s : Finset (ℕ × ℕ)) (ε : ℝ) (hε : 0 < ε) :
       ∃ (ι : Type) (_ : Fintype ι)
         (c : ι → ℂ) (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ),
         -- finite sum approximant Φs
         (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
           ((∑ i, c i • ψ i) - ΦK) < ε ∧
         ‖(∑ i, c i * T (ψ i)) - ∫ x in K, T (f x • g x)‖ < ε
   ```

   This lemma may be proved by a measurable finite-partition approximation of
   `boundedKernel g f` in the scalar seminorm `p_s`. The finite measure fact
   `isFiniteMeasure_restrict_of_isBounded` is the measure-theory input.

3. Diagonalize the finite-seminorm approximations into one sequence `Φn`.
   Use the finite set

   ```lean
   Finset.Icc (0, 0) (N, N)  -- or equivalent finite box of `(k,n)` indices
   ```

   and error tolerance `(1 / (N + 1 : ℝ))`. This gives a sequence satisfying all
   individual seminorm convergence goals.

4. Define the scalar sequence by the same finite data:

   ```lean
   In N := ∑ i, cN i * T (ψN i)
   ```

   Then `hstep` is exactly `clm_finset_weighted_sum_exchange`.

5. Prove `In → ∫ x in K, T (f x • g x)` from the same finite-approximation
   construction. The scalar domination is already available via
   `integrable_schwartz_fubini_clm_weighted_kernel`.

6. Apply
   `bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants`.

If this route becomes too large, split out the genuinely general theorem:

```lean
theorem exists_simple_approx_integral_for_countable_seminorms
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p : ℕ → Seminorm ℝ E)
    ...
```

but do this only if the concrete Schwartz-space version becomes unwieldy. A
concrete theorem over `SchwartzMap (Fin m → ℝ) ℂ` is preferable for now because
all domination lemmas are already specialized to Schwartz seminorms.

### Proof Of The Blocker Theorem

The blocker theorem should be proved by diagonalizing finite-seminorm
approximations. The proof naturally splits into one analytic approximation lemma
and one formal diagonalization theorem.

#### Analytic Input

First prove the following finite-seminorm approximation lemma. This is the real
analytic content: finite measurable partitions approximate the bounded kernel in
the finite seminorm envelope and simultaneously approximate the scalar
`T`-integral.

```lean
lemma exists_finite_seminorm_kernel_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (s : Finset (ℕ × ℕ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ) (I : ℂ),
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < ε ∧
      ‖I - ∫ x in K, T (f x • g x)‖ < ε ∧
      T Φ = I
```

Proof of this finite lemma:

The useful implementation route is not an abstract Bochner simple-function
approximation. Instead, use compact uniform approximation on the bounded
parameter set. Since the parameter space `Fin m → ℝ` is finite-dimensional,
`hK_bdd` makes `closure K` compact. The map

```lean
F x := f x • g x
```

is continuous into `SchwartzMap`, so every finite Schwartz-seminorm envelope is
uniformly continuous on `closure K`.

#### Step A: choose the controlling seminorms

First extract a finite Schwartz-seminorm bound for `T`:

```lean
obtain ⟨sT, CT, hCT_pos, hT_bound⟩ :=
  clm_norm_le_finite_schwartz_seminorms_complex T
```

For the scalar estimate we need to control `‖T ψ‖`, while for the Schwartz
estimate we need the user-provided finite set `s`. Use the combined finite set:

```lean
let u : Finset (ℕ × ℕ) := s ∪ sT
let p : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
  u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
```

Because the complex and real Schwartz seminorms agree here,
`schwartz_seminorm_complex_eq_real` lets `hT_bound` be applied after bounding by
`p`.

Choose a small positive local tolerance `η`. A safe choice is

```lean
let M : ℝ := max 1 ((volume.restrict K) Set.univ).toReal
let B : ℝ := max 1 CT
let η : ℝ := ε / (2 * M * B)
```

with helper facts:

```lean
have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
have hη_pos : 0 < η := by positivity
```

The constants can be made less compressed in Lean if `positivity` needs help.
The only mathematical requirement is:

```lean
((volume.restrict K) Set.univ).toReal * η < ε
CT * ((volume.restrict K) Set.univ).toReal * η < ε
```

#### Step B: finite partition approximation

Prove the following helper. This is the actual partition lemma needed for the
blocker.

```lean
lemma exists_finite_partition_schwartz_kernel_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (u : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) :
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → Set (Fin m → ℝ))
      (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ i, MeasurableSet (A i)) ∧
      Set.PairwiseDisjoint Set.univ A ∧
      K ⊆ ⋃ i, A i ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i x, x ∈ A i →
        (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (ψ i - f x • g x) < η)
```

Proof of the helper:

1. Let `C := closure K`. Use `hK_bdd.isCompact_closure` or the available
   finite-dimensional compactness API to get `hC : IsCompact C`.
2. Define `F x := f x • g x`. Its continuity is:

   ```lean
   have hF_cont : Continuous fun x => f x • g x :=
     f.continuous.smul hg_cont
   ```

3. For each `y ∈ C`, continuity of

   ```lean
   fun x => (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
     ((f y • g y) - (f x • g x))
   ```

   gives an open neighborhood `U y` of `y` where this seminorm is `< η`.
4. Compactness of `C` gives finitely many centers `y i` whose neighborhoods
   cover `C`. Set `ψ i := f (y i) • g (y i)`.
5. Turn the finite open cover into a disjoint measurable partition of `K`:

   ```lean
   A 0     := K ∩ U 0
   A (j+1) := K ∩ U (j+1) \ ⋃ i ≤ j, U i
   ```

   In Lean, it is usually easier to index by a finite set `c : Finset α` from
   the compactness subcover, define cells over `c.attach`, and use
   `Finset.biUnion` for the previous cells. The cells are measurable because
   `K` is measurable and each `U i` is open.

This helper avoids needing a measurable-space or normed-space instance on
`SchwartzMap`; it only uses continuity of finitely many real-valued seminorm
functions.

#### Step C: build the finite approximant

After applying the partition helper to the combined finite set `u`, define:

```lean
let μ := volume.restrict K
let c : ι → ℂ := fun i => ((μ (A i)).toReal : ℂ)
let Φ : SchwartzMap (Fin m → ℝ) ℂ := ∑ i, c i • ψ i
let I : ℂ := ∑ i, c i * T (ψ i)
```

Then:

```lean
have hstep : T Φ = I := by
  simpa [Φ, I, c] using clm_finset_weighted_sum_exchange T Finset.univ c ψ
```

This is the third conjunct of `exists_finite_seminorm_kernel_approx`.

#### Step D: prove the Schwartz-seminorm estimate

For each individual seminorm index `(k,n) ∈ s`, prove:

```lean
lemma partition_approx_seminorm_le {k n : ℕ} (hkn : (k,n) ∈ s) :
    SchwartzMap.seminorm ℝ k n (Φ - ΦK)
      ≤ ∫ x in K,
          SchwartzMap.seminorm ℝ k n
            ((piecewiseKernel A ψ x) - f x • g x)
```

Here `piecewiseKernel A ψ x` is the finite-valued function that equals `ψ i` on
cell `A i`. This helper should be proved by unfolding the seminorm:

1. Use `boundedParamIntegralScalar_iteratedFDeriv_eq` to rewrite derivatives of
   `ΦK`.
2. Use linearity of `iteratedFDeriv` on the finite sum defining `Φ`.
3. For each `ξ`, rewrite the derivative difference as a finite sum/integral
   over the partition:

   ```lean
   iteratedFDeriv ℝ n (fun ξ => (Φ - ΦK) ξ) ξ
     =
       ∑ i, ∫ x in A i,
         iteratedFDeriv ℝ n
           (fun ζ => (ψ i - f x • g x) ζ) ξ
   ```

4. Apply `norm_sum_le`, `norm_integral_le_integral_norm`, and
   `SchwartzMap.le_seminorm` to obtain:

   ```lean
   ‖ξ‖ ^ k * ‖...‖
     ≤ ∫ x in K,
         SchwartzMap.seminorm ℝ k n
           (piecewiseKernel A ψ x - f x • g x)
   ```

5. Package the pointwise-in-`ξ` bound back into
   `SchwartzMap.seminorm ℝ k n`.

Then pass from individual seminorms to the finite supremum:

```lean
have hp_le :
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK)
      ≤ ∫ x in K,
          (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
            (piecewiseKernel A ψ x - f x • g x) := by
  exact Seminorm.finset_sup_apply_le ?nonneg fun kn hkn =>
    partition_approx_seminorm_le K hK_meas ... hkn
```

The partition helper gives the pointwise bound by `η`, so:

```lean
have hp_small :
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK)
      < ε := by
  calc
    (s.sup family) (Φ - ΦK)
        ≤ ∫ x in K, (s.sup family) (piecewiseKernel A ψ x - f x • g x) := hp_le
    _ ≤ ∫ x in K, η := integral_mono_of_forall ...
    _ = ((volume.restrict K) Set.univ).toReal * η := by simp [μ]
    _ < ε := hη_chosen_for_s
```

If the combined seminorm `u` was used in the partition helper, first bound
`s.sup family ≤ u.sup family` by `Finset.le_sup` and `Finset.mem_union_left`.

#### Step E: prove the scalar estimate

The scalar estimate is parallel, but easier because `T` is already linear and
continuous:

```lean
have hscalar_le :
    ‖I - ∫ x in K, T (f x • g x)‖
      ≤ ∫ x in K,
          ‖T (piecewiseKernel A ψ x - f x • g x)‖
```

Proof:

1. Rewrite `I` as the integral over the partition:

   ```lean
   I = ∑ i, ∫ x in A i, T (ψ i)
   ```

2. Rewrite the target integral as the sum over the partition:

   ```lean
   ∫ x in K, T (f x • g x)
     = ∑ i, ∫ x in A i, T (f x • g x)
   ```

3. Subtract the sums and use linearity:

   ```lean
   I - ∫ x in K, T (f x • g x)
     = ∑ i, ∫ x in A i, T (ψ i - f x • g x)
   ```

4. Apply `norm_sum_le` and `norm_integral_le_integral_norm`.

Now dominate the integrand using `hT_bound`. Since `sT ⊆ u`,

```lean
have hT_point (x) :
    ‖T (piecewiseKernel A ψ x - f x • g x)‖
      ≤ CT *
        (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (piecewiseKernel A ψ x - f x • g x)
```

The partition helper bounds the `u`-sup by `η`; therefore:

```lean
have hscalar_small :
    ‖I - ∫ x in K, T (f x • g x)‖ < ε := by
  calc
    ‖I - ∫ x in K, T (f x • g x)‖
        ≤ ∫ x in K, ‖T (piecewiseKernel A ψ x - f x • g x)‖ := hscalar_le
    _ ≤ ∫ x in K,
          CT * (u.sup family) (piecewiseKernel A ψ x - f x • g x) :=
        integral_mono_of_forall ...
    _ ≤ ∫ x in K, CT * η := integral_mono_of_forall ...
    _ = CT * ((volume.restrict K) Set.univ).toReal * η := by ring_nf
    _ < ε := hη_chosen_for_T
```

#### Step F: finish the finite lemma

Return:

```lean
exact ⟨Φ, I, hp_small, hscalar_small, hstep⟩
```

The finite lemma should be implemented before the unconditional blocker theorem.
It is the only place where finite partitions and integral-over-partition
bookkeeping are needed.

#### Diagonalization Code

Status: the diagonal/limit part is now implemented and builds in
[`SchwartzFubini.lean`](/Users/annamei/Documents/GitHub/OSreconstruction/OSReconstruction/GeneralResults/SchwartzFubini.lean:978).
The implementation deliberately keeps the unresolved analytic input as an
explicit hypothesis `hfinite`; it does not add a new axiom.

The implemented theorem is:

```lean
theorem exists_bounded_kernel_approximants_of_finite_seminorm_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (hfinite :
      ∀ (ΦK : SchwartzMap (Fin m → ℝ) ℂ),
        (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) →
        ∀ (s : Finset (ℕ × ℕ)) (ε : ℝ), 0 < ε →
          ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ) (I : ℂ),
            (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < ε ∧
            ‖I - ∫ x in K, T (f x • g x)‖ < ε ∧
            T Φ = I) :
    ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
      (∀ k n,
        Filter.Tendsto
          (fun N => SchwartzMap.seminorm ℝ k n
            (Φn N -
              Classical.choose
                (bounded_parameter_integral_scalar_is_schwartz
                  K hK_meas hK_bdd g f hg_cont hg_bound)))
          Filter.atTop (nhds 0)) ∧
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))) ∧
      ∀ N, T (Φn N) = In N
```

It uses a finite box of seminorm indices:

```lean
def schwartzSeminormIndexBox (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1)).product (Finset.range (N + 1))

lemma mem_schwartzSeminormIndexBox {k n N : ℕ}
    (hk : k ≤ N) (hn : n ≤ N) :
    (k, n) ∈ schwartzSeminormIndexBox N := by
  simp [schwartzSeminormIndexBox, hk, hn]

lemma schwartzSeminorm_le_finset_sup {m : ℕ}
    (s : Finset (ℕ × ℕ)) {k n : ℕ} (hmem : (k, n) ∈ s)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ k n ψ ≤
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
  exact (Finset.le_sup
    (f := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
    hmem) ψ
```

Proof structure:

- Choose `ΦK` using `bounded_parameter_integral_scalar_is_schwartz`.
- For each `N`, call `hfinite` with
  `s = schwartzSeminormIndexBox N` and `ε = (N + 1 : ℝ)⁻¹`.
- Define `Φn N` and `In N` from these choices.
- For fixed seminorm `(k,n)`, eventually `k,n ≤ N`, so
  `SchwartzMap.seminorm ℝ k n (Φn N - ΦK)` is bounded by the finite supremum
  over `schwartzSeminormIndexBox N`.
- Use `exists_nat_one_div_lt` and `inv_le_inv₀` to show
  `(N + 1 : ℝ)⁻¹ → 0`.
- The scalar convergence of `In` is the same reciprocal estimate applied to
  `‖In N - ∫ x in K, T (f x • g x)‖`.

Build check for this refinement:

```bash
lake build OSReconstruction.GeneralResults.SchwartzFubini
```

This build passes, with only pre-existing linter/deprecation warnings.

This proof is the intended code path for the blocker. Once it compiles, the
unconditional bounded-set exchange is obtained by the short theorem in the next
section.

### Complete Proof Code Once The Blocker Exists

The following code is the complete proof of the bounded-set exchange from the
approximant theorem. The first four declarations are already implemented and
compile in `SchwartzFubini.lean`. The final theorem is the intended replacement
for the bounded-set exchange step once `exists_bounded_kernel_approximants` is
proved.

```lean
def boundedKernel {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ :=
  fun x => f x • g x

lemma isFiniteMeasure_restrict_of_isBounded {m : ℕ}
    (K : Set (Fin m → ℝ)) (hK_bdd : Bornology.IsBounded K) :
    IsFiniteMeasure (volume.restrict K) := by
  rw [isFiniteMeasure_restrict]
  exact (ne_of_lt hK_bdd.measure_lt_top)

theorem bounded_parameter_integral_schwartz_clm_exchange_of_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (_hK_meas : MeasurableSet K)
    (_hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (_g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (_f : SchwartzMap (Fin m → ℝ) ℂ)
    (_hg_cont : Continuous _g)
    (_hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (_g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K _g _f ξ)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (In : ℕ → ℂ)
    (hΦn : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n (Φn N - ΦK))
        Filter.atTop (nhds 0))
    (hIn :
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (_f x • _g x))))
    (hstep : ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K _g _f ξ) ∧
      T ΦK = ∫ x in K, T (_g x) * _f x := by
  refine ⟨ΦK, hΦK, ?_⟩
  have hΦn_top : Filter.Tendsto Φn Filter.atTop (nhds ΦK) :=
    tendsto_schwartz_atTop_of_tendsto_seminorm hΦn
  have hT_eq_weighted :
      T ΦK = ∫ x in K, T (_f x • _g x) :=
    clm_exchange_of_tendsto_approximants
      T ΦK Φn In (∫ x in K, T (_f x • _g x))
      hΦn_top hIn hstep
  calc
    T ΦK = ∫ x in K, T (_f x • _g x) := hT_eq_weighted
    _ = ∫ x in K, T (_g x) * _f x :=
        integral_clm_weighted_kernel_eq_pairing K T _g _f

theorem bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (In : ℕ → ℂ)
    (hΦn : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n
          (Φn N -
            Classical.choose
              (bounded_parameter_integral_scalar_is_schwartz
                K hK_meas hK_bdd g f hg_cont hg_bound)))
        Filter.atTop (nhds 0))
    (hIn :
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))))
    (hstep : ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  let ΦK : SchwartzMap (Fin m → ℝ) ℂ :=
    Classical.choose
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  have hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ :=
    Classical.choose_spec
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      ΦK hΦK Φn In hΦn hIn hstep

theorem bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (happrox :
      ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
        (∀ k n,
          Filter.Tendsto
            (fun N => SchwartzMap.seminorm ℝ k n
              (Φn N -
                Classical.choose
                  (bounded_parameter_integral_scalar_is_schwartz
                    K hK_meas hK_bdd g f hg_cont hg_bound)))
            Filter.atTop (nhds 0)) ∧
        Filter.Tendsto In Filter.atTop
          (nhds (∫ x in K, T (f x • g x))) ∧
        ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  rcases happrox with ⟨Φn, In, hΦn, hIn, hstep⟩
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      Φn In hΦn hIn hstep
```

Once `exists_bounded_kernel_approximants` is proved, the bounded-set exchange
theorem is the following short proof:

```lean
theorem bounded_parameter_integral_schwartz_clm_exchange {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      (exists_bounded_kernel_approximants
        K hK_meas hK_bdd T g f hg_cont hg_bound)
```

The only non-filled identifier in that final proof is
`exists_bounded_kernel_approximants`; that is the real blocker theorem described
above.

### Load-Bearing `T` Exchange On Bounded Sets

The equality

```lean
T ΦK = ∫ x in K, T (g x) * f x
```

should be proved by a simple-function approximation inside the bounded-set
constructor. On compact pieces, a Riemann/partition formulation is an
equivalent route, but for bounded measurable sets the simple-function language
matches the measure-theory API better:

1. Approximate the scalar-weighted Schwartz-valued map
   `x ↦ f x • g x` on `K` by finite sums
   `Σ j, μ(K_j) • (f x_j • g x_j)` in every Schwartz seminorm.
2. The same finite sums converge pointwise after applying `T`, because `T` is
   continuous and linear.
3. The scalar functions `x ↦ T (g x) * f x` are integrable by Phase 1, so the
   scalar simple-function sums converge to the set integral.
4. Identify the two limits.

This is the recommended route. Do not try to represent `T` by a Schwartz
kernel; a general continuous linear functional on Schwartz space is a tempered
distribution, not a pointwise kernel.

## Phase 3: Tail Estimates In Schwartz Seminorms

The main Cauchy estimate is:

```lean
lemma seminorm_fubini_tail_le {m : ℕ}
    (R S : ℕ) (hRS : R ≤ S)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (Φ_S - Φ_R)
      ≤ ∫ x in fubiniCube m S \ fubiniCube m R,
          ‖f x‖ * SchwartzMap.seminorm ℝ k n (g x)
```

Then combine it with `hg_bound k n`:

```lean
‖f x‖ * SchwartzMap.seminorm ℝ k n (g x)
  ≤ const * ‖f x‖ * (1 + ‖x‖)^N
```

The right-hand side is integrable by Schwartz decay of `f`, so its tails tend
to zero. This gives:

```lean
lemma fubini_truncations_cauchy_schwartz {m : ℕ} :
    CauchySeq Φ_R
```

Use `schwartz_withSeminorms.tendsto_nhds` or the Cauchy characterization from
`SchwartzComplete.lean`: prove Cauchy in every seminorm.

Because Phase 2 is stated for bounded measurable sets, treat
`Φ_S - Φ_R` as the bounded-set integral over
`fubiniCube m S \ fubiniCube m R`. If the implementation instead keeps the
constructor compact-only, add a separate pointwise-uniqueness lemma identifying
`Φ_S - Φ_R` with the annulus integral before proving the tail bound.

## Phase 4: Completeness And Definition Of `Φ`

From `CauchySeq Φ_R` and completeness:

```lean
obtain ⟨Φ, hΦ_lim⟩ := cauchySeq_tendsto_of_complete hΦ_cauchy
```

Then prove the pointwise identity:

```lean
∀ ξ, Φ ξ = ∫ x, g x ξ * f x
```

Proof:

- Evaluation at a point is continuous on Schwartz space; use the explicit
  bound `SchwartzMap.norm_le_seminorm ℝ φ ξ` rather than introducing an
  unnecessary standalone API unless the proof becomes repetitive.
- Therefore `Φ_R ξ → Φ ξ`.
- Separately, by scalar dominated convergence / exhaustion convergence,
  ```lean
  (∫ x in fubiniCube m R, g x ξ * f x) →
    ∫ x, g x ξ * f x
  ```
  using `integrable_schwartz_fubini_pointwise`.
- Conclude by uniqueness of limits.

## Phase 5: Exchange With `T`

For every `R`, use the bounded-set constructor from Phase 2 to get the
truncated exchange:

```lean
T Φ_R = ∫ x in fubiniCube m R, T (g x) * f x
```

Then pass to the limit:

- `T Φ_R → T Φ` by `T.continuous`.
- `∫ x in fubiniCube m R, T (g x) * f x →
   ∫ x, T (g x) * f x`
  by exhaustion convergence and
  `integrable_schwartz_fubini_clm_pairing`.
- Conclude by uniqueness of scalar limits.

The nontrivial work has already happened in Phase 2: the bounded-set
constructor proves the `T` exchange by simple-function approximation
and continuity of `T`.

## Suggested Lemma Order

Implement and verify in this order:

1. Done: import `DiffUnderIntegralSchwartz`.
2. Done: prove `integrable_schwartz_fubini_pointwise`.
3. Done: prove `clm_polyGrowth_of_seminorm_polyGrowth`.
4. Done: prove `integrable_schwartz_fubini_clm_pairing`.
5. Done: prove `fubiniCube` closedness, measurability, monotonicity,
   boundedness, exhaustion, and scalar integral convergence.
6. Done: add `integrableOn_schwartz_fubini_pointwise`,
   `integrableOn_schwartz_fubini_clm_pairing`, and
   `boundedParamIntegralScalar`.
7. Done: prove `continuous_schwartz_iteratedFDeriv_eval`.
8. Done: prove `integrable_polyGrowth_mul_schwartz_norm`.
9. Done: prove `integrable_schwartz_fubini_seminorm_weight`.
10. Done: add `boundedParamIntegralDeriv`.
11. Done: prove `integrableOn_boundedParamIntegral_iterated_deriv_kernel`.
12. Done: prove raw `boundedParamIntegralDeriv_hasFDerivAt`.
13. Done: prove the curry/integral bridge and
   `boundedParamIntegralDeriv_hasFDerivAt_curry`.
14. Done: prove `boundedParamIntegralScalar_iteratedFDeriv_eq`.
15. Done: prove `bounded_parameter_integral_scalar_is_schwartz`, with
   `boundedParamIntegralScalar_contDiff` and
   `boundedParamIntegralScalar_decay_bound`.
16. Done: prove `clm_norm_le_finite_schwartz_seminorms`.
17. Done: prove `integrable_schwartz_fubini_finset_sum_seminorm_weight`.
18. Done: prove `clm_norm_le_finite_schwartz_seminorms_complex`.
19. Done: prove `integrable_schwartz_fubini_finset_sum_seminorm_weight_complex`
   and `clm_weighted_kernel_norm_le_finset_sum`.
20. Done: prove `integrable_schwartz_fubini_clm_weighted_kernel` and
   `integrableOn_schwartz_fubini_clm_weighted_kernel`.
21. Done: prove `clm_finset_weighted_sum_exchange`,
   `clm_weighted_kernel_apply`, and `integral_clm_weighted_kernel_eq_pairing`.
22. Done: prove `clm_exchange_of_tendsto_approximants`.
23. Done: prove `tendsto_schwartz_atTop_iff_seminorm` and
   `tendsto_schwartz_atTop_of_tendsto_seminorm`.
24. Done: prove `boundedKernel`,
   `bounded_parameter_integral_schwartz_clm_exchange_of_approximants`,
   `bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants`,
   and `bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants`.
25. Done: prove `isFiniteMeasure_restrict_of_isBounded`.
26. Next: construct simple/finite approximants for `x ↦ f x • g x` on bounded
   `K` and prove Schwartz-topology convergence to `ΦK`.
27. Next: prove the measurable bounded-kernel domination/exchange helper for
   simple-function approximation on `K`.
28. Next: prove `bounded_parameter_integral_schwartz_clm_exchange`, with the
   `T` exchange justified by the same simple-function approximation/limit used
   to construct `ΦK`.
29. Next: prove the tail estimate `seminorm_fubini_tail_le`.
30. Next: prove the Cauchy property for `Φ_R`.
31. Next: identify the limit `Φ` pointwise.
32. Next: pass the `T` exchange to the limit.
33. Final: replace the axiom with a theorem.

## Important Technical Notes

- Avoid trying to use a Bochner integral directly into `SchwartzMap` unless a
  normed model of that space is introduced. The current topology is generated
  by seminorms, so seminorm Cauchy estimates are the natural route.
- Keep the statement over `Fin m → ℝ`; downstream wrappers such as
  `schwartz_clm_fubini_exchange_real` already reduce mixed-domain cases to this
  same-domain theorem.
- Do not use downstream Wightman or SCV analytic facts. The result is pure
  functional analysis for Schwartz space.
- The bounded-set integral theorem is the largest missing local API. Once it
  returns both the pointwise formula and the `T` exchange formula, the global
  proof is mostly tail estimates and limit uniqueness.
- Inline continuity facts when possible: `x ↦ seminorm k n (g x)` is
  `((schwartz_withSeminorms ℝ _ ℂ).continuous_seminorm (k, n)).comp hg_cont`.
  Evaluation estimates should generally use `SchwartzMap.norm_le_seminorm`.

## Expected Risk

The highest-risk part is proving the bounded-parameter integral is a
`SchwartzMap` with the right derivative/seminorm bounds and the matching
`T` exchange. If that becomes too
large, split it into a reusable theorem:

```lean
theorem schwartz_integral_of_bounded_param
    ...
```

and prove `schwartz_clm_fubini_exchange` as a short application of that theorem
plus the tail/completeness argument.
