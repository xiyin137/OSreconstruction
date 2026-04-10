/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.DualCone
import OSReconstruction.SCV.LaplaceSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier Support in Dual Cones

This file defines `HasFourierSupportInDualCone`, the multi-dimensional generalization
of `HasOneSidedFourierSupport` from `PaleyWiener.lean`. A tempered distribution T
has Fourier support in the dual cone C* if T vanishes on all Schwartz test functions
whose Fourier transform is supported outside C*.

The main theorem `fourierSupportInDualCone_of_tube_boundaryValue` shows that
the distributional boundary value of a tube-holomorphic function with tempered BV
has Fourier support in the dual cone.

## Status

This file contains the Fourier-support predicate and elementary cone lemmas used
by the Paley-Wiener-Schwartz development. The full theorem
`fourierSupportInDualCone_of_tube_boundaryValue` is currently postulated as an
interface theorem: its honest proof needs the Phase 3 Fourier-Laplace bridge,
not just the boundary-value statement in this file.

## References

- Vladimirov, "Methods of the Theory of Generalized Functions", §25
- Streater-Wightman, "PCT, Spin and Statistics, and All That", Theorem 2-6
-/

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory SchwartzMap Complex
noncomputable section

variable {m : ℕ}

/-! ### Dual cone for flat types -/

/-- The dual cone of a set S ⊆ ℝ^m using the standard dot product on `Fin m → ℝ`.
    This is the flat-type version of `DualConeEucl`, compatible with `SchwartzMap`
    and `fourierTransformCLM` which use `Fin m → ℝ` (not `EuclideanSpace`). -/
def DualConeFlat (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {ξ | ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i}

theorem mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ} :
    ξ ∈ DualConeFlat S ↔ ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i :=
  Iff.rfl

/-! ### Fourier support predicate -/

/-- A tempered distribution `T` has Fourier support in a closed set `S` if
    `T` vanishes on all Schwartz test functions whose support is disjoint from `S`.

    More precisely: for every φ ∈ S(ℝ^m) with `supp(φ) ∩ S = ∅`, we have `T(φ) = 0`.

    This is the "frequency-side" version: `T` is the Fourier transform of the
    original distribution, and `S` is the support in frequency space.
    The connection to `fourierTransformCLM` is made in individual theorems,
    not baked into the definition, to avoid `InnerProductSpace` requirements
    on `Fin m → ℝ`. -/
def HasFourierSupportIn (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
    (∀ x ∈ Function.support (φ : (Fin m → ℝ) → ℂ), x ∉ S) →
    T φ = 0

/-- A tempered distribution `T` has Fourier support in the dual cone `C*` of a set `S`. -/
def HasFourierSupportInDualCone (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  HasFourierSupportIn (DualConeFlat S) T

/-! ### Dual cone membership negation -/

/-- If ξ is not in the dual cone of S, there exists y ∈ S with negative pairing.
    This is just the negation of the universal quantifier in the definition. -/
theorem exists_neg_pairing_of_not_mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ}
    (hξ : ξ ∉ DualConeFlat S) :
    ∃ y ∈ S, ∑ i, y i * ξ i < 0 := by
  simp only [DualConeFlat, Set.mem_setOf_eq, not_forall, not_le] at hξ
  obtain ⟨y, hy, hlt⟩ := hξ
  exact ⟨y, hy, hlt⟩

/-! ### Basic properties -/

theorem hasFourierSupportIn_mono {S₁ S₂ : Set (Fin m → ℝ)}
    (h : S₁ ⊆ S₂)
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hT : HasFourierSupportIn S₁ T) :
    HasFourierSupportIn S₂ T :=
  fun φ hφ => hT φ (fun x hx hxS₁ => hφ x hx (h hxS₁))

/-- If T has Fourier support in S, then T agrees on test functions that coincide on S. -/
theorem hasFourierSupportIn_eqOn {S : Set (Fin m → ℝ)}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hT : HasFourierSupportIn S T)
    {φ ψ : SchwartzMap (Fin m → ℝ) ℂ}
    (h_eq : ∀ x ∈ S, (φ : (Fin m → ℝ) → ℂ) x = (ψ : (Fin m → ℝ) → ℂ) x) :
    T φ = T ψ := by
  have hsub : T (φ - ψ) = 0 := by
    apply hT
    intro x hx hxS
    simp only [SchwartzMap.sub_apply, Function.mem_support, ne_eq] at hx
    exact hx (sub_eq_zero.mpr (h_eq x hxS))
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hsub)

/-! ### Slice functionals -/

/-- The inverse Fourier transform on `Fin m → ℝ`, transported through
    `EuclideanSpace ℝ (Fin m)` so it can use Mathlib's Schwartz-space Fourier
    transform. This is the frequency-side test-function map appearing in the
    Paley-Wiener-Schwartz boundary-value theorem. -/
noncomputable def inverseFourierFlatSupportCLM {m : ℕ} :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let ft : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ
  fromEuc.comp (ft.comp toEuc)

/-- The "slice functional" at imaginary part `y ∈ C`: integration of `F(x+iy)` against
    a Schwartz test function. This is well-defined because `F` is holomorphic (hence
    continuous) on the tube interior, and Schwartz functions are integrable. -/
def sliceFunctional
    (F : (Fin m → ℂ) → ℂ)
    (y : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) : ℂ :=
  ∫ x : Fin m → ℝ, F (fun i => (x i : ℂ) + (y i : ℂ) * I) * f x

/-! ### Boundary-value slice lemma -/

/-- The BV limit connects `sliceFunctional` to `W`. -/
theorem sliceFunctional_tendsto_bv
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => sliceFunctional F (ε • η) φ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)) := by
  refine Filter.Tendsto.congr ?_ (hF_bv η hη φ)
  intro ε
  show ∫ x, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x =
    sliceFunctional F (ε • η) φ
  simp only [sliceFunctional]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x =
    F (fun i => ↑(x i) + ↑((ε • η) i) * I) * φ x
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-! ### The main theorem -/

/-- **Textbook support theorem, packaged in project terms.**

    If `F` is holomorphic on the tube `T(C)` over an open convex salient cone and has
    tempered distributional boundary values `W`, and `F` satisfies a Vladimirov-type
    moderate-growth bound on the tube, then those boundary values are realized by some
    tempered distribution whose Fourier support lies in the dual cone `C*`.

    This is the SCV theorem one actually needs before the support conclusion below:
    it identifies the boundary-value functional with the inverse-Fourier pairing of a
    dual-cone-supported tempered distribution. The mathematical content is standard
    Vladimirov/Hörmander Fourier-Laplace theory; the Lean surface is phrased using the
    project's `TubeDomain`, `SchwartzMap`, and `HasFourierSupportInDualCone` notions. -/
axiom tube_boundaryValue_realizes_dualCone_distribution
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_growth : ∃ (C_bd : ℝ) (N q : ℕ), C_bd > 0 ∧
      ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
        ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ q)
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    ∃ (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone C T ∧
      ∀ (η : Fin m → ℝ), η ∈ C →
        ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
          Filter.Tendsto
            (fun ε : ℝ => ∫ x : Fin m → ℝ,
              F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (T (inverseFourierFlatSupportCLM φ)))

/-- **Frequency-side dual-cone support from tube boundary values.**

    Tube-holomorphic `F` with tempered BV `W`, under Vladimirov-type moderate growth,
    admits a frequency-side tempered distribution `T` with support in `C*` such that
    `W φ = T(FT⁻¹ φ)` for every Schwartz test function `φ`.

    Proof sketch:
    1. The BV hypothesis gives W as the distributional limit of ∫ F(x+iεη)φ(x)dx.
    2. By `tube_boundaryValue_realizes_dualCone_distribution`, the same limit equals
       `T(FT⁻¹ φ)` for an appropriate `T` with support in `C*`.
    3. Limits in `ℂ` are unique, so `W φ = T(FT⁻¹ φ)` pointwise. -/
theorem fourierSupportInDualCone_of_tube_boundaryValue
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_growth : ∃ (C_bd : ℝ) (N q : ℕ), C_bd > 0 ∧
      ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
        ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ q)
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    ∃ (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone C T ∧
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        W φ = T (inverseFourierFlatSupportCLM φ) := by
  obtain ⟨T, hT_supp, hT_bv⟩ := tube_boundaryValue_realizes_dualCone_distribution
    hC_open hC_conv hC_cone hC_salient hC_ne hF_holo hF_growth hF_bv
  refine ⟨T, hT_supp, fun φ => ?_⟩
  obtain ⟨η, hη⟩ := hC_ne
  exact tendsto_nhds_unique (hF_bv η hη φ) (hT_bv η hη φ)

end
