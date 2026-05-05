/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

/-!
# Wick-rotated boundary pairing equals the Wightman functional

This file establishes the **W-to-integral bridge** for OPTR-supported
test functions:

```
wickRotatedBoundaryPairing Wfn n f = Wfn.W n f      (single block)
```

and its joint version, needed to prove `W_analytic_cluster_integral`
(the integral-form OS-axiom E4) directly from `Wfn.cluster` (the R4
axiom field).

## Why this bridge

The R→E direction's E4 verification needs cluster of the constructed
Schwinger functions in *un-reflected* integral form
`∫ F_ext(wick x)(f.tensorProduct g_a)(x) dx`. The R4 axiom field
`Wfn.cluster` already gives un-reflected cluster at the W-evaluation
level for arbitrary Schwartz tests. The missing bridge is the equality
between the W evaluation and the Wick-rotated integral on
OPTR-supported test functions.

## Strategy

A one-parameter holomorphic deformation. Define
```
g(s) := ∫ W_analytic(x + i s · η(x)) f(x) dx,    s ∈ (0, 1]
```
where `η(x) = (x⁰, 0⃗)` is the Wick-rotation imaginary direction.

* `g(1)` is the Wick-rotated integral (= `wickRotatedBoundaryPairing`).
* `lim_{s → 0⁺} g(s) = Wfn.W n f` by `bhw_distributional_boundary_values`
  (after a slicing reduction: `η` is `x`-dependent, but since
  `η(x) = (x⁰, 0⃗)` only depends on `x⁰`, slicing on time-coordinates
  reduces to constant-`η` boundary value lemmas).
* `g'(s) = 0` on `(0, 1]` by Cauchy-Riemann + IBP in time, using
  Schwartz decay at spatial infinity and the OPTR support of `f`
  (which makes `f` vanish at the τ = 0 boundary).
* FTC on `[ε, 1]` for any `ε > 0` ⟹ `g 1 = g ε`. Take `ε → 0⁺`.

## Discharge plan and key lemmas

1. `wick_OPTR_in_forwardTube` — for OPTR-supported `x`, `wick(x)` lies
   in `ForwardTube d n`. Trivial consequence of OPTR's positive-ordered
   times.

2. `g_deform_deriv_zero` — the deformation has zero `s`-derivative on
   `(0, 1]`. This is the heart: differentiate under the integral via
   Mathlib's dominated derivative-under-integral, apply Cauchy-Riemann
   to convert to a real-direction derivative, IBP in time. Boundary
   terms vanish at spatial infinity (Schwartz) and at `τ = 0` (OPTR
   support).

3. `g_deform_one_eq_pairing` — `g(1) = wickRotatedBoundaryPairing Wfn n f`.
   Direct unfolding plus `F_ext_on_translatedPET_total_eq_on_PET`.

4. `g_deform_tendsto_W` — `g(s) → Wfn.W n f` as `s → 0⁺`. Reduces to
   `bhw_distributional_boundary_values` via slicing.

5. `wickRotatedBoundaryPairing_eq_W` — the bridge theorem, by combining
   the above.

## Joint case

The joint version `wickRotatedBoundaryPairing_eq_W_joint` for
`f.tensorProduct g_a` (with `f` on n points, `g_a` on m, both
OPTR-supported, spatial `a`) decomposes by permutation: the joint
Wick-rotated config lies in PET (Permuted Extended Tube) but not
generally in `ForwardTube` because inter-block time ordering is
unconstrained. We split `NPointDomain d (n+m)` into pieces by which
permutation of (n+m) puts the joint config into `ForwardTube`, apply
the single-block bridge per piece, and reassemble using
`F_ext_on_translatedPET_total_perm_invariant` and `Wfn.hermitian` /
permutation symmetry.

## References

* OS 1973 §2 (Schwinger families on `𝒮_<`)
* Glimm-Jaffe Chapter 19 (Wightman → Schwinger via BHW)
* Streater-Wightman Chapter 3
* See `docs/wick_rotated_pairing_eq_W_plan.md` for the full plan.
-/

open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-! ### Step 1: OPTR Wick-rotates into the forward tube -/

/-- For OPTR-supported configurations, the Wick rotation lands in the
forward tube. Concretely, if `x : NPointDomain d n` has strictly
increasing positive times `0 < x_1⁰ < x_2⁰ < ⋯ < x_n⁰`, then the
Wick-rotated point `wickRotatePoint ∘ x` (so each component's time
becomes `i x_k⁰`) lies in `ForwardTube d n`: every successive
imaginary-time difference `x_{k+1}⁰ - x_k⁰` is positive, hence in `V₊`.

This is a thin wrapper around `euclidean_ordered_in_forwardTube` that
extracts the two real-valued hypotheses (positive times + strictly
increasing times) from OPTR membership. -/
theorem wick_OPTR_in_forwardTube
    (n : ℕ) (x : NPointDomain d n)
    (hx : x ∈ OrderedPositiveTimeRegion d n) :
    (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
  euclidean_ordered_in_forwardTube x
    (fun k j hkj => (hx k).2 j hkj)
    (fun k => (hx k).1)

/-! ### Step 2: the deformation `g(s)` and its zero derivative -/

/-- The one-parameter holomorphic deformation between the boundary
distribution form (`s → 0⁺`) and the Wick-rotated integral (`s = 1`).

For a fixed Wightman family `Wfn`, an arity `n`, a Schwartz test
function `f`, and a deformation parameter `s : ℝ`, define the
time-component path
```
z₀(s, x⁰) := (1 - s) · x⁰ + s · i · x⁰ = x⁰ · ((1 - s) + i s),
```
which interpolates between `x⁰` (real, at `s = 0`, the boundary value)
and `i x⁰` (imaginary, at `s = 1`, the Wick rotation). The spatial
components are unchanged.

```
g_deform s := ∫_x (W_analytic_BHW Wfn n).val (z(s, x)) · f(x)
```
where `z(s, x) k μ = z₀(s, x_k⁰)` for `μ = 0` and `z(s, x) k μ = x_k^μ`
for `μ ≥ 1`. -/
noncomputable def g_deform
    (Wfn : WightmanFunctions d) (n : ℕ) (f : SchwartzNPoint d n)
    (s : ℝ) : ℂ :=
  ∫ x : NPointDomain d n,
    (W_analytic_BHW Wfn n).val
      (fun k μ => (x k μ : ℂ) +
        (s : ℂ) * (if μ = 0 then (Complex.I - 1) * (x k 0 : ℂ) else 0)) *
    (f x)

/-- The deformation function has zero derivative in `s` on `(0, 1]`,
when `f` is OPTR-supported.

**Proof outline**:

1. Differentiate under the integral via
   `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
   The dominator is `(spectrum_condition's polynomial bound) · |f|`
   times Schwartz seminorms — integrable on the OPTR support.

2. The pointwise `s`-derivative of the integrand is
   `i · η(x) · ∇_z (W_analytic_BHW Wfn n).val · f(x)`.

3. By Cauchy-Riemann (holomorphicity of `W_analytic_BHW` on
   `ForwardTube` — proved via `(W_analytic_BHW Wfn n).property`
   field 1), the imaginary-direction derivative equals
   `i · ∂_t (W_analytic_BHW Wfn n).val`.

4. Integrate by parts in the time variables. Boundary contributions:
   * `t → ±∞`: vanish by Schwartz decay of `f`.
   * `t = 0⁺`: vanish because `f` has tsupport in OPTR (so
     `f → 0` as any time coordinate approaches 0).

5. After IBP, the integrand collapses by holomorphicity to `0`.

**Note**: this is the technically heaviest step. Length estimate:
~150–250 Lean lines depending on how cleanly we can chain the
Cauchy-Riemann / IBP machinery on Schwartz tests. -/
theorem g_deform_deriv_zero
    (Wfn : WightmanFunctions d) (n : ℕ)
    (f : SchwartzNPoint d n)
    (hsupp : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (s : ℝ) (_hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    HasDerivAt (g_deform Wfn n f) 0 s := by
  sorry

/-! ### Step 3: the deformation at `s = 1` is the Wick-rotated pairing -/

/-- At `s = 1`, the deformation `g_deform` coincides with
`wickRotatedBoundaryPairing` for OPTR-supported test functions.

**Proof**: pointwise equality of the integrands.
* On `x ∈ OPTR`: the deformed argument coincides with
  `wickRotatePoint`. By `wick_OPTR_in_forwardTube` plus the inclusion
  `ForwardTube ⊆ PermutedExtendedTube`, the Wick-rotated config lies
  in PET. Then `F_ext_on_translatedPET_total_eq_on_PET` identifies
  `F_ext_on_translatedPET_total` with `(W_analytic_BHW Wfn n).val`.
* On `x ∉ OPTR`: `f x = 0` by the support hypothesis (`tsupport f ⊆
  OPTR` ⟹ `support f ⊆ OPTR`), so both integrands vanish. -/
theorem g_deform_one_eq_pairing
    (Wfn : WightmanFunctions d) (n : ℕ)
    (f : SchwartzNPoint d n)
    (hsupp : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    g_deform Wfn n f 1 = wickRotatedBoundaryPairing Wfn n f := by
  unfold g_deform wickRotatedBoundaryPairing
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  -- Pointwise: deformed-arg evaluation of W_analytic_BHW * f x
  --          = F_ext_on_translatedPET_total at wickRotatePoint x * f x.
  by_cases hx : x ∈ OrderedPositiveTimeRegion d n
  · -- x ∈ OPTR: deformed argument at s=1 equals wickRotatePoint x pointwise.
    have h_arg : ∀ k μ,
        ((x k μ : ℂ) + ((1 : ℝ) : ℂ) *
          (if μ = 0 then (Complex.I - 1) * (x k 0 : ℂ) else 0)) =
        wickRotatePoint (x k) μ := by
      intro k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [wickRotatePoint]
        ring
      · simp [wickRotatePoint, hμ]
    -- Wick rotation lands in ForwardTube ⊆ PermutedExtendedTube.
    have h_wick_FT : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
      wick_OPTR_in_forwardTube n x hx
    -- Convert FT to PET via euclidean_distinct_in_permutedTube.
    have h_wick_PET : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n :=
      euclidean_distinct_in_permutedTube x
        (fun i j hij => by
          rcases lt_trichotomy i j with hlt | heq | hgt
          · exact ne_of_lt ((hx i).2 j hlt)
          · exact (hij heq).elim
          · exact ne_of_gt ((hx j).2 i hgt))
        (fun i => (hx i).1)
    -- F_ext = W_analytic on PET.
    have h_F_ext_eq :
        F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) =
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) :=
      F_ext_on_translatedPET_total_eq_on_PET Wfn _ h_wick_PET
    -- Pointwise equality of arguments → equality of W_analytic_BHW evaluations.
    have h_W_eq :
        (W_analytic_BHW Wfn n).val
          (fun k μ => (x k μ : ℂ) + ((1 : ℝ) : ℂ) *
            (if μ = 0 then (Complex.I - 1) * (x k 0 : ℂ) else 0)) =
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) := by
      apply congrArg
      funext k μ
      exact h_arg k μ
    show (W_analytic_BHW Wfn n).val
        (fun k μ => (x k μ : ℂ) + ((1 : ℝ) : ℂ) *
          (if μ = 0 then (Complex.I - 1) * (x k 0 : ℂ) else 0)) *
        (f : NPointDomain d n → ℂ) x =
      F_ext_on_translatedPET_total Wfn (fun k => wickRotatePoint (x k)) *
        (f : NPointDomain d n → ℂ) x
    rw [h_W_eq, h_F_ext_eq]
  · -- x ∉ OPTR: f x = 0 by support hypothesis.
    have h_notInTsupp : x ∉ tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
      fun hxts => hx (hsupp hxts)
    have hf_zero : (f : NPointDomain d n → ℂ) x = 0 :=
      image_eq_zero_of_notMem_tsupport h_notInTsupp
    simp [hf_zero]

/-! ### Step 4: the deformation tends to the Wightman functional -/

/-- As `s → 0⁺`, the deformation `g_deform` converges to `Wfn.W n f`.

**Proof outline**: reduce to `bhw_distributional_boundary_values` via
slicing on the time-coordinate hyperplanes. The full Wick direction
`η(x) = (x⁰, 0⃗)` is `x`-dependent, but `bhw_distributional_boundary_values`
is for constant `η` in the forward cone. Slice the OPTR support by
diagonals where `η` is locally constant, apply the constant-`η`
boundary-value lemma per slice, sum/integrate via Fubini.

Alternative formulation: prove a generalized boundary-value lemma
allowing `η` to depend on `x` (through the time coordinates) within
the forward cone. More uniform but new infrastructure. The slicing
approach is the path of least resistance — see plan doc. -/
theorem g_deform_tendsto_W
    (Wfn : WightmanFunctions d) (n : ℕ)
    (f : SchwartzNPoint d n)
    (hsupp : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    Filter.Tendsto (g_deform Wfn n f) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Wfn.W n f)) := by
  sorry

/-! ### Step 5: assembly — the W-to-integral bridge -/

/-- **The W-to-integral bridge**: for OPTR-supported test functions,
the Wick-rotated boundary pairing equals the Wightman functional.

```
wickRotatedBoundaryPairing Wfn n f = Wfn.W n f
```

This is the missing piece for proving `W_analytic_cluster_integral`
(the integral-form E4 cluster on the constructed Schwinger functions)
directly from `Wfn.cluster` (the R4 axiom field).

**Proof**: by deformation invariance. `g_deform` has zero `s`-derivative
on `(0, 1]`, so by the FTC on `[ε, 1]` for any `ε > 0`, `g_deform 1 =
g_deform ε`. Taking `ε → 0⁺`, `g_deform ε → Wfn.W n f`. Therefore
`g_deform 1 = Wfn.W n f`, and `g_deform 1` equals the Wick-rotated
pairing by `g_deform_one_eq_pairing`. -/
theorem wickRotatedBoundaryPairing_eq_W
    (Wfn : WightmanFunctions d) (n : ℕ)
    (f : SchwartzNPoint d n)
    (hsupp : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    wickRotatedBoundaryPairing Wfn n f = Wfn.W n f := by
  sorry

/-! ### Joint case (for `W_analytic_cluster_integral`)

The joint version handles the configuration of `f.tensorProduct g_a`
where `f, g` are OPTR-supported separately and `a` is a purely spatial
translation.

**Subtlety**: separately OPTR-supported `f` (on the first n points) and
`g_a` (on the last m points after spatial translation) do NOT guarantee
that the joint config has globally ordered times. The joint
Wick-rotated config thus lies in `TranslatedPET d (n+m)` (a permuted
forward tube under translation), not necessarily in `ForwardTube d (n+m)`.

**Strategy**: decompose the integration domain by permutation.
`NPointDomain d (n+m) = ⋃_σ R_σ` where `R_σ` is the region where the
joint config, after permutation `σ`, lies in `ForwardTube`. On each
`R_σ` apply `F_ext_on_translatedPET_total_perm_invariant` + the
single-block bridge (post-permutation). Reassemble using
`Wfn.hermitian` / Wightman symmetry to identify all permutation values
with the un-permuted `Wfn.W (n+m)` evaluation. -/

/-- **Joint version of the W-to-integral bridge.**

For OPTR-supported `f, g` separately and a purely spatial translation
`a`, the joint Wick-rotated boundary pairing of `f.tensorProduct g_a`
equals the Wightman functional value.

**Discharge**: see strategy comment above. ~100–150 Lean lines on
top of the single-block case. -/
theorem wickRotatedBoundaryPairing_eq_W_joint
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (a : SpacetimeDim d) (_ha0 : a 0 = 0)
    (g_a : SchwartzNPoint d m)
    (_hga : ∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) :
    wickRotatedBoundaryPairing Wfn (n + m) (f.tensorProduct g_a) =
      Wfn.W (n + m) (f.tensorProduct g_a) := by
  sorry

end OSReconstruction
