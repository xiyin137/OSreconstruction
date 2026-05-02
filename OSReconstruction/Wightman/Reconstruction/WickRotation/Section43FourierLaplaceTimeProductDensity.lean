import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct

/-!
# Section 4.3 finite time-product density

This file contains the finite-product density step for the Section 4.3
Fourier-Laplace OS route.  The analytic construction of the multitime compact
Laplace transform lives in `Section43FourierLaplaceTimeProduct`; here we only
package its linearity and use the one-variable density theorem coordinatewise.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Quotient equality in the one-variable positive-energy codomain is equality
on the closed nonnegative half-line. -/
theorem eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq
    {f g : SchwartzMap ℝ ℂ}
    (hfg :
      section43PositiveEnergyQuotientMap1D f =
        section43PositiveEnergyQuotientMap1D g) :
    Set.EqOn (f : ℝ → ℂ) (g : ℝ → ℂ) (Set.Ici (0 : ℝ)) := by
  change (Submodule.Quotient.mk f : Section43PositiveEnergy1D) =
    Submodule.Quotient.mk g at hfg
  rw [Submodule.Quotient.eq] at hfg
  intro x hx
  have hx0 : ((f - g : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := hfg hx
  exact sub_eq_zero.mp <| by simpa using hx0

/-- The raw finite-time Laplace scalar is additive in the compact source. -/
theorem section43IteratedLaplaceRaw_add
    (n : ℕ) (g h : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    section43IteratedLaplaceRaw n (g + h) σ =
      section43IteratedLaplaceRaw n g σ +
        section43IteratedLaplaceRaw n h σ := by
  unfold section43IteratedLaplaceRaw
  calc
    (∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (g + h).f τ)
        =
      ∫ τ : Fin n → ℝ,
        (Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ +
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * h.f τ) := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          change
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
                (g.f τ + h.f τ) =
              Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ +
                Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * h.f τ
          ring
    _ =
      (∫ τ : Fin n → ℝ,
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ) +
      (∫ τ : Fin n → ℝ,
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * h.f τ) := by
          rw [integral_add
            (integrable_section43IteratedLaplaceRaw_integrand_of_compact n g σ)
            (integrable_section43IteratedLaplaceRaw_integrand_of_compact n h σ)]

/-- The raw finite-time Laplace scalar is homogeneous in the compact source. -/
theorem section43IteratedLaplaceRaw_smul
    (n : ℕ) (c : ℂ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    section43IteratedLaplaceRaw n (c • g) σ =
      c * section43IteratedLaplaceRaw n g σ := by
  unfold section43IteratedLaplaceRaw
  calc
    (∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (c • g).f τ)
        =
      ∫ τ : Fin n → ℝ,
        c * (Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ) := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          change
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
                (c * g.f τ) =
              c * (Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ)
          ring
    _ =
      c * ∫ τ : Fin n → ℝ,
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ := by
          simpa using
            (integral_const_mul c
              (fun τ : Fin n → ℝ =>
                Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) * g.f τ))

/-- Representatives of multitime Laplace transforms add pointwise on the
positive finite-time quotient surface. -/
theorem section43IteratedLaplaceRepresentative_add
    {n : ℕ} {g h : Section43CompactStrictPositiveTimeSource n}
    {Φ Ψ : SchwartzMap (Fin n → ℝ) ℂ}
    (hΦ : section43IteratedLaplaceRepresentative n g Φ)
    (hΨ : section43IteratedLaplaceRepresentative n h Ψ) :
    section43IteratedLaplaceRepresentative n (g + h) (Φ + Ψ) := by
  intro σ hσ
  calc
    (Φ + Ψ) σ = Φ σ + Ψ σ := by simp
    _ = section43IteratedLaplaceRaw n g σ +
        section43IteratedLaplaceRaw n h σ := by
          rw [hΦ σ hσ, hΨ σ hσ]
    _ = section43IteratedLaplaceRaw n (g + h) σ := by
          rw [section43IteratedLaplaceRaw_add]

/-- Representatives of multitime Laplace transforms are homogeneous pointwise
on the positive finite-time quotient surface. -/
theorem section43IteratedLaplaceRepresentative_smul
    {n : ℕ} (c : ℂ) {g : Section43CompactStrictPositiveTimeSource n}
    {Φ : SchwartzMap (Fin n → ℝ) ℂ}
    (hΦ : section43IteratedLaplaceRepresentative n g Φ) :
    section43IteratedLaplaceRepresentative n (c • g) (c • Φ) := by
  intro σ hσ
  calc
    (c • Φ) σ = c * Φ σ := by simp
    _ = c * section43IteratedLaplaceRaw n g σ := by
          rw [hΦ σ hσ]
    _ = section43IteratedLaplaceRaw n (c • g) σ := by
          rw [section43IteratedLaplaceRaw_smul]

/-- The compact multitime Laplace transform is additive in its compact source. -/
theorem section43IteratedLaplaceCompactTransform_map_add
    {n : ℕ} (g h : Section43CompactStrictPositiveTimeSource n) :
    section43IteratedLaplaceCompactTransform n (g + h) =
      section43IteratedLaplaceCompactTransform n g +
        section43IteratedLaplaceCompactTransform n h := by
  let Φg := section43IteratedLaplaceSchwartzRepresentative n g
  let Φh := section43IteratedLaplaceSchwartzRepresentative n h
  have hΦg : section43IteratedLaplaceRepresentative n g Φg := by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
  have hΦh : section43IteratedLaplaceRepresentative n h Φh := by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem h hσ
  have hsum : section43IteratedLaplaceRepresentative n (g + h) (Φg + Φh) :=
    section43IteratedLaplaceRepresentative_add hΦg hΦh
  calc
    section43IteratedLaplaceCompactTransform n (g + h)
        = section43TimePositiveQuotientMap n (Φg + Φh) :=
            section43IteratedLaplaceCompactTransform_eq_quotient n (g + h)
              (Φg + Φh) hsum
    _ = section43TimePositiveQuotientMap n Φg +
        section43TimePositiveQuotientMap n Φh := by
          rw [map_add]
    _ = section43IteratedLaplaceCompactTransform n g +
        section43IteratedLaplaceCompactTransform n h := by
          rw [← section43IteratedLaplaceCompactTransform_eq_quotient n g Φg hΦg,
            ← section43IteratedLaplaceCompactTransform_eq_quotient n h Φh hΦh]

/-- The compact multitime Laplace transform is homogeneous in its compact
source. -/
theorem section43IteratedLaplaceCompactTransform_map_smul
    {n : ℕ} (c : ℂ) (g : Section43CompactStrictPositiveTimeSource n) :
    section43IteratedLaplaceCompactTransform n (c • g) =
      c • section43IteratedLaplaceCompactTransform n g := by
  let Φg := section43IteratedLaplaceSchwartzRepresentative n g
  have hΦg : section43IteratedLaplaceRepresentative n g Φg := by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
  have hsmul : section43IteratedLaplaceRepresentative n (c • g) (c • Φg) :=
    section43IteratedLaplaceRepresentative_smul c hΦg
  calc
    section43IteratedLaplaceCompactTransform n (c • g)
        = section43TimePositiveQuotientMap n (c • Φg) :=
            section43IteratedLaplaceCompactTransform_eq_quotient n (c • g)
              (c • Φg) hsmul
    _ = c • section43TimePositiveQuotientMap n Φg := by
          rw [map_smul]
    _ = c • section43IteratedLaplaceCompactTransform n g := by
          rw [← section43IteratedLaplaceCompactTransform_eq_quotient n g Φg hΦg]

/-- The compact strict-positive multitime Laplace transform as a linear map.
This exposes its range as the submodule needed for the finite-product density
argument. -/
noncomputable def section43IteratedLaplaceCompactTransformLinearMap
    (n : ℕ) :
    Section43CompactStrictPositiveTimeSource n →ₗ[ℂ]
      Section43TimePositiveComponent n where
  toFun := section43IteratedLaplaceCompactTransform n
  map_add' := section43IteratedLaplaceCompactTransform_map_add
  map_smul' := section43IteratedLaplaceCompactTransform_map_smul

/-- A product tensor whose one-variable factors lie in the one-sided compact
Laplace preimage lies in the finite-time compact transform preimage. -/
theorem section43TimeProductTensor_mem_iteratedLaplaceCompactTransform_preimage
    {n : ℕ} {fs : Fin n → SchwartzMap ℝ ℂ}
    (hfs :
      ∀ i : Fin n,
        fs i ∈
          section43PositiveEnergyQuotientMap1D ⁻¹'
            Set.range section43OneSidedLaplaceCompactTransform1D) :
    section43TimeProductTensor fs ∈
      (section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n) := by
  classical
  have hEx :
      ∀ i : Fin n,
        ∃ g : Section43CompactPositiveTimeSource1D,
          section43OneSidedLaplaceCompactTransform1D g =
            section43PositiveEnergyQuotientMap1D (fs i) := by
    intro i
    exact hfs i
  choose gs hgs using hEx
  refine ⟨section43TimeProductSource gs, ?_⟩
  calc
    section43IteratedLaplaceCompactTransform n (section43TimeProductSource gs)
        =
      section43TimePositiveQuotientMap n
        (section43TimeProductTensor
          (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
          section43IteratedLaplaceCompactTransform_productSource gs
    _ = section43TimePositiveQuotientMap n (section43TimeProductTensor fs) := by
          apply section43TimePositiveQuotientMap_eq_of_eqOn_region
          intro σ hσ
          rw [section43TimeProductTensor, section43TimeProductTensor]
          rw [SchwartzMap.productTensor_apply, SchwartzMap.productTensor_apply]
          refine Finset.prod_congr rfl ?_
          intro i _hi
          have hq :
              section43PositiveEnergyQuotientMap1D (fs i) =
                section43PositiveEnergyQuotientMap1D
                  (section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) := by
            calc
              section43PositiveEnergyQuotientMap1D (fs i)
                  = section43OneSidedLaplaceCompactTransform1D (gs i) :=
                    (hgs i).symm
              _ = section43PositiveEnergyQuotientMap1D
                    (section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) :=
                    section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient (gs i)
          have heqOn :=
            eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq
          exact (heqOn (hσ i)).symm

/-- Finite-time compact strict-positive Laplace transforms have dense preimage
under the positive-time quotient map. -/
theorem dense_section43IteratedLaplaceCompactTransform_preimage
    (n : ℕ) :
    Dense
      ((section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n)) := by
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let E := SchwartzMap ℝ ℂ
  let S1 : Set E :=
    section43PositiveEnergyQuotientMap1D ⁻¹'
      Set.range section43OneSidedLaplaceCompactTransform1D
  let PS : Set A :=
    {F : A | ∃ fs : Fin n → E,
      (∀ i : Fin n, fs i ∈ S1) ∧ F = section43TimeProductTensor fs}
  let MS : Submodule ℂ A := Submodule.span ℂ PS
  let qn := section43TimePositiveQuotientMap n
  let L := section43IteratedLaplaceCompactTransformLinearMap n
  let Mq : Submodule ℂ (Section43TimePositiveComponent n) := LinearMap.range L
  let target : Submodule ℂ A := Mq.comap qn.toLinearMap
  have htarget :
      (section43TimePositiveQuotientMap n) ⁻¹'
          Set.range (section43IteratedLaplaceCompactTransform n) =
        (target : Set A) := by
    ext F
    simp [target, Mq, L, qn, section43IteratedLaplaceCompactTransformLinearMap]
  have hMS_dense : Dense (MS : Set A) := by
    simpa [MS, PS, S1, A, E] using
      section43_timeProductTensor_span_dense_of_factor_dense
        (S := S1)
        dense_section43OneSidedLaplaceCompactTransform1D_preimage n
  have hMS_le_target_sub : MS ≤ target := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨fs, hfs, rfl⟩
    change qn (section43TimeProductTensor fs) ∈ Mq
    have hprod :=
      section43TimeProductTensor_mem_iteratedLaplaceCompactTransform_preimage
        (n := n) (fs := fs) hfs
    change section43TimePositiveQuotientMap n (section43TimeProductTensor fs) ∈
      Set.range (section43IteratedLaplaceCompactTransform n) at hprod
    rcases hprod with ⟨g, hg⟩
    exact ⟨g, by
      simpa [Mq, L, section43IteratedLaplaceCompactTransformLinearMap] using hg⟩
  rw [htarget]
  exact Dense.mono (fun F hF => hMS_le_target_sub hF) hMS_dense

/-- The finite-time compact strict-positive Laplace transform has dense range
in the finite-time positive-energy quotient. -/
theorem denseRange_section43IteratedLaplaceCompactTransformLinearMap
    (n : ℕ) :
    DenseRange (section43IteratedLaplaceCompactTransformLinearMap n) := by
  have hq :
      IsOpenQuotientMap
        (section43TimePositiveQuotientMap n :
          SchwartzMap (Fin n → ℝ) ℂ → Section43TimePositiveComponent n) := by
    simpa [section43TimePositiveQuotientMap] using
      (section43TimeVanishingSubmodule n).isOpenQuotientMap_mkQ
  have hdense_set :
      Dense (Set.range (section43IteratedLaplaceCompactTransform n)) :=
    hq.dense_preimage_iff.mp
      (dense_section43IteratedLaplaceCompactTransform_preimage n)
  simpa [DenseRange, section43IteratedLaplaceCompactTransformLinearMap] using
    hdense_set

end OSReconstruction
