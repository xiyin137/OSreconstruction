import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProduct
import OSReconstruction.SCV.DenseBoundaryExtension

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

/-- Multiplication by a product cutoff preserves the finite-time product-tensor
form.

This is the algebraic bridge used in local-window density arguments: after a
global product approximation has been multiplied by a product cutoff, it is
still an honest product source, with each one-variable factor cut off
separately. -/
theorem section43TimeProductTensor_cutoff_productTensor
    {n : ℕ} (χs fs : Fin n → SchwartzMap ℝ ℂ) :
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs)
        (section43TimeProductTensor fs) =
      section43TimeProductTensor
        (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((section43TimeProductTensor χs :
      SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ))
    (section43TimeProductTensor χs).hasTemperateGrowth
    (section43TimeProductTensor fs) x]
  rw [section43TimeProductTensor, SchwartzMap.productTensor_apply]
  have hfactor :
      ∀ i : Fin n,
        (SchwartzMap.smulLeftCLM ℂ (χs i) (fs i)) (x i) =
          (χs i) (x i) * (fs i) (x i) := by
    intro i
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (g := ((χs i : SchwartzMap ℝ ℂ) : ℝ → ℂ))
      (χs i).hasTemperateGrowth (fs i) (x i)]
    simp [smul_eq_mul]
  simp [section43TimeProductTensor, SchwartzMap.productTensor_apply,
    hfactor, smul_eq_mul, Finset.prod_mul_distrib]

/-- General support control for finite-time product tensors.  The compact-source
support lemma in `Section43FourierLaplaceTimeProduct` is this statement
specialized to one-sided compact time sources. -/
theorem tsupport_section43TimeProductTensor_subset_pi_tsupport_schwartz
    {n : ℕ} (fs : Fin n → SchwartzMap ℝ ℂ) :
    tsupport
      ((section43TimeProductTensor fs :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ)
      ⊆ {x | ∀ i : Fin n, x i ∈ tsupport ((fs i) : ℝ → ℂ)} := by
  intro x hx i
  by_contra hxi
  have hlocal :
      ((fs i : SchwartzMap ℝ ℂ) : ℝ → ℂ) =ᶠ[𝓝 (x i)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxi
  have hcoord :
      Tendsto (fun y : Fin n → ℝ => y i) (𝓝 x) (𝓝 (x i)) :=
    (continuous_apply i).continuousAt
  have hlocal_pi :
      ∀ᶠ y in 𝓝 x, (fs i) (y i) = 0 :=
    hcoord.eventually hlocal
  have hprod_zero :
      ((section43TimeProductTensor fs :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hlocal_pi] with y hy
    rw [section43TimeProductTensor, SchwartzMap.productTensor_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hy
  exact (notMem_tsupport_iff_eventuallyEq.mpr hprod_zero) hx

/-- A product cutoff localizes the dense global product span without losing
product shape.

This is the closure form needed before imposing Lemma 5.1 window support on
product Laplace generators: multiplying an arbitrary finite-time Schwartz test
by a product cutoff puts it in the closure of the span of product tensors whose
one-variable factors have been cut off individually. -/
theorem section43_productCutoff_mem_closure_cutoffProductSpan
    {n : ℕ} (χs : Fin n → SchwartzMap ℝ ℂ)
    (F : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F ∈
      (((Submodule.span ℂ
        {G : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            G =
              section43TimeProductTensor
                (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i))}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S_all : Set A :=
    {G : A | ∃ fs : Fin n → SchwartzMap ℝ ℂ, G = section43TimeProductTensor fs}
  let S_cut : Set A :=
    {G : A |
      ∃ fs : Fin n → SchwartzMap ℝ ℂ,
        G =
          section43TimeProductTensor
            (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i))}
  let M_all : Submodule ℂ A := Submodule.span ℂ S_all
  let M_cut : Submodule ℂ A := Submodule.span ℂ S_cut
  let T : A →L[ℂ] A :=
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs)
  have hM_all_dense : Dense (M_all : Set A) := by
    simpa [M_all, S_all, A] using section43_timeProductTensor_span_dense n
  have hImage : M_all ≤ M_cut.topologicalClosure.comap T.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    intro G hG
    rcases hG with ⟨fs, rfl⟩
    change T (section43TimeProductTensor fs) ∈ M_cut.topologicalClosure
    apply subset_closure
    refine Submodule.subset_span ?_
    refine ⟨fs, ?_⟩
    simpa [T, S_cut] using
      (section43TimeProductTensor_cutoff_productTensor χs fs)
  have hclosed :
      IsClosed
        ((M_cut.topologicalClosure.comap T.toLinearMap : Submodule ℂ A) :
          Set A) := by
    change IsClosed ((T : A → A) ⁻¹' (M_cut.topologicalClosure : Set A))
    exact M_cut.isClosed_topologicalClosure.preimage T.continuous
  have hclosure_le :
      M_all.topologicalClosure ≤ M_cut.topologicalClosure.comap T.toLinearMap :=
    Submodule.topologicalClosure_minimal M_all hImage hclosed
  have htop :
      (⊤ : Submodule ℂ A) ≤ M_cut.topologicalClosure.comap T.toLinearMap := by
    rw [← (Submodule.dense_iff_topologicalClosure_eq_top).mp hM_all_dense]
    exact hclosure_le
  have hmem : F ∈ M_cut.topologicalClosure.comap T.toLinearMap := htop (by simp)
  simpa [T, M_cut, S_cut, A] using hmem

/-- Cutting an arbitrary one-variable Schwartz factor by a compact
strict-positive cutoff gives a compact positive one-dimensional source. -/
noncomputable def section43CompactPositiveTimeSource1D_of_cutoff
    (χ f : SchwartzMap ℝ ℂ)
    (hχ_pos : tsupport (χ : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : HasCompactSupport (χ : ℝ → ℂ)) :
    Section43CompactPositiveTimeSource1D where
  f := SchwartzMap.smulLeftCLM ℂ (χ : ℝ → ℂ) f
  positive := by
    intro x hx
    exact hχ_pos
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ) (g := (χ : ℝ → ℂ)) (f := f) hx).2)
  compact := by
    refine HasCompactSupport.of_support_subset_isCompact hχ_compact.isCompact ?_
    intro x hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ) (g := (χ : ℝ → ℂ)) (f := f)
        (subset_tsupport _ hx)).2)

/-- Source-side localization form: if the one-variable cutoffs are compact and
strict-positive, the product cutoff of any finite-time Schwartz source is in
the closure of the span of honest compact positive product sources. -/
theorem section43_productCutoff_mem_closure_productSourceSpan
    {n : ℕ}
    (χs : Fin n → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin n, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin n, HasCompactSupport ((χs i) : ℝ → ℂ))
    (F : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F ∈
      (((Submodule.span ℂ
        {G : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
            G = (section43TimeProductSource gs).f}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S_cut : Set A :=
    {G : A |
      ∃ fs : Fin n → SchwartzMap ℝ ℂ,
        G =
          section43TimeProductTensor
            (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i))}
  let S_src : Set A :=
    {G : A |
      ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
        G = (section43TimeProductSource gs).f}
  let M_cut : Submodule ℂ A := Submodule.span ℂ S_cut
  let M_src : Submodule ℂ A := Submodule.span ℂ S_src
  have hcut :
      SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F ∈
        (M_cut.topologicalClosure : Set A) := by
    simpa [M_cut, S_cut, A] using
      section43_productCutoff_mem_closure_cutoffProductSpan χs F
  have hM_cut_le_src : M_cut ≤ M_src := by
    refine Submodule.span_le.mpr ?_
    intro G hG
    rcases hG with ⟨fs, rfl⟩
    refine Submodule.subset_span ?_
    let gs : Fin n → Section43CompactPositiveTimeSource1D := fun i =>
      section43CompactPositiveTimeSource1D_of_cutoff
        (χs i) (fs i) (hχ_pos i) (hχ_compact i)
    refine ⟨gs, ?_⟩
    rfl
  exact Submodule.topologicalClosure_mono hM_cut_le_src hcut

/-- Support-carrying source-side localization.  If the product of the
one-variable cutoff supports lies in a window `U`, the dense product-source
approximants can be chosen with source support inside `U`. -/
theorem section43_productCutoff_mem_closure_productSourceSpan_of_cutoffSupport
    {n : ℕ}
    (χs : Fin n → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin n, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin n, HasCompactSupport ((χs i) : ℝ → ℂ))
    {U : Set (Fin n → ℝ)}
    (hχ_U :
      ∀ τ : Fin n → ℝ,
        (∀ i : Fin n, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ U)
    (F : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F ∈
      (((Submodule.span ℂ
        {G : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs).f :
                (Fin n → ℝ) → ℂ) ⊆ U ∧
            G = (section43TimeProductSource gs).f}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S_cut : Set A :=
    {G : A |
      ∃ fs : Fin n → SchwartzMap ℝ ℂ,
        G =
          section43TimeProductTensor
            (fun i => SchwartzMap.smulLeftCLM ℂ (χs i) (fs i))}
  let S_src : Set A :=
    {G : A |
      ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
            (Fin n → ℝ) → ℂ) ⊆ U ∧
        G = (section43TimeProductSource gs).f}
  let M_cut : Submodule ℂ A := Submodule.span ℂ S_cut
  let M_src : Submodule ℂ A := Submodule.span ℂ S_src
  have hcut :
      SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F ∈
        (M_cut.topologicalClosure : Set A) := by
    simpa [M_cut, S_cut, A] using
      section43_productCutoff_mem_closure_cutoffProductSpan χs F
  have hM_cut_le_src : M_cut ≤ M_src := by
    refine Submodule.span_le.mpr ?_
    intro G hG
    rcases hG with ⟨fs, rfl⟩
    refine Submodule.subset_span ?_
    let gs : Fin n → Section43CompactPositiveTimeSource1D := fun i =>
      section43CompactPositiveTimeSource1D_of_cutoff
        (χs i) (fs i) (hχ_pos i) (hχ_compact i)
    refine ⟨gs, ?_, ?_⟩
    · intro τ hτ
      apply hχ_U
      intro i
      have hτi :
          τ i ∈ tsupport (((gs i).f : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
        tsupport_section43TimeProductTensor_subset_pi_tsupport gs hτ i
      exact
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ) (g := ((χs i : SchwartzMap ℝ ℂ) : ℝ → ℂ)) (f := fs i)
          hτi).2)
    · rfl
  exact Submodule.topologicalClosure_mono hM_cut_le_src hcut

theorem section43_productCutoff_smul_eq_self_of_one_on_tsupport
    {n : ℕ} (χs : Fin n → SchwartzMap ℝ ℂ)
    (F : SchwartzMap (Fin n → ℝ) ℂ)
    (hχ_one :
      ∀ x ∈ tsupport (F : (Fin n → ℝ) → ℂ),
        section43TimeProductTensor χs x = 1) :
    SchwartzMap.smulLeftCLM ℂ (section43TimeProductTensor χs) F = F := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (g := ((section43TimeProductTensor χs :
      SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ))
    (section43TimeProductTensor χs).hasTemperateGrowth F x]
  by_cases hx : x ∈ tsupport (F : (Fin n → ℝ) → ℂ)
  · simp [smul_eq_mul, hχ_one x hx]
  · have hFx : F x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [smul_eq_mul, hFx]

/-- Local source density after an actual product cutoff has been selected:
if the cutoff is one on the source support and its product support lies in the
window `U`, then the source itself is in the closure of product sources
supported in `U`. -/
theorem section43_mem_closure_productSourceSpan_of_productCutoffSupport
    {n : ℕ}
    (χs : Fin n → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin n, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin n, HasCompactSupport ((χs i) : ℝ → ℂ))
    {U : Set (Fin n → ℝ)}
    (hχ_U :
      ∀ τ : Fin n → ℝ,
        (∀ i : Fin n, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ U)
    (F : SchwartzMap (Fin n → ℝ) ℂ)
    (hχ_one :
      ∀ x ∈ tsupport (F : (Fin n → ℝ) → ℂ),
        section43TimeProductTensor χs x = 1) :
    F ∈
      (((Submodule.span ℂ
        {G : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
            tsupport ((section43TimeProductSource gs).f :
                (Fin n → ℝ) → ℂ) ⊆ U ∧
            G = (section43TimeProductSource gs).f}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  have hmem :=
    section43_productCutoff_mem_closure_productSourceSpan_of_cutoffSupport
      χs hχ_pos hχ_compact hχ_U F
  rwa [section43_productCutoff_smul_eq_self_of_one_on_tsupport
    χs F hχ_one] at hmem

/-- Local equality from membership in the closure of supported product sources.

This is the equality analogue of
`section43_tendsto_timeSchwartz_of_mem_closure_supportedProductSources`: if two
finite-time Schwartz CLMs agree on every compact positive product source
supported in the same local window, then they agree on every test already in
the corresponding closed product-source span. -/
theorem section43_timeCLM_eq_of_mem_closure_supportedProductSources
    (n : ℕ)
    (T U : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    {Window : Set (Fin n → ℝ)}
    {F : SchwartzMap (Fin n → ℝ) ℂ}
    (hF :
      F ∈
        (((Submodule.span ℂ
          {G : SchwartzMap (Fin n → ℝ) ℂ |
            ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
              tsupport ((section43TimeProductSource gs).f :
                  (Fin n → ℝ) → ℂ) ⊆ Window ∧
              G = (section43TimeProductSource gs).f}) :
          Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
          Set (SchwartzMap (Fin n → ℝ) ℂ)))
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin n → ℝ) → ℂ) ⊆ Window →
        T (section43TimeProductSource gs).f =
          U (section43TimeProductSource gs).f) :
    T F = U F := by
  classical
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let D : Set A :=
    {G : A |
      ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
            (Fin n → ℝ) → ℂ) ⊆ Window ∧
        G = (section43TimeProductSource gs).f}
  let L : A →L[ℂ] ℂ := T - U
  let K : Submodule ℂ A := LinearMap.ker L.toLinearMap
  have hD_sub : D ⊆ (K : Set A) := by
    intro G hG
    rcases hG with ⟨gs, hgs, rfl⟩
    change L (section43TimeProductSource gs).f = 0
    rw [ContinuousLinearMap.sub_apply, h_on_products gs hgs, sub_self]
  have hspan_sub :
      ((Submodule.span ℂ D : Submodule ℂ A) : Set A) ⊆ (K : Set A) :=
    Submodule.span_le.mpr hD_sub
  have hK_closed : IsClosed (K : Set A) := by
    change IsClosed (L ⁻¹' ({0} : Set ℂ))
    exact isClosed_singleton.preimage L.continuous
  have hclosure_sub :
      closure ((Submodule.span ℂ D : Submodule ℂ A) : Set A) ⊆
        (K : Set A) :=
    closure_minimal hspan_sub hK_closed
  have hFK : F ∈ (K : Set A) := by
    exact hclosure_sub (by simpa [D, A] using hF)
  have hzero : L F = 0 := by
    simpa [K] using hFK
  simpa [L, sub_eq_zero] using hzero

/-- Product-cutoff form of the localized same-distribution handoff.

If a product cutoff is one on a test and its product support lies in the local
window where two CLMs agree on compact positive product sources, then the two
CLMs agree on that test. -/
theorem section43_timeCLM_eq_of_productCutoff_supportedProductSources
    {n : ℕ}
    (T U : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    {Window : Set (Fin n → ℝ)}
    (χs : Fin n → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin n, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin n, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_Window :
      ∀ τ : Fin n → ℝ,
        (∀ i : Fin n, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ Window)
    (F : SchwartzMap (Fin n → ℝ) ℂ)
    (hχ_one :
      ∀ x ∈ tsupport (F : (Fin n → ℝ) → ℂ),
        section43TimeProductTensor χs x = 1)
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin n → ℝ) → ℂ) ⊆ Window →
        T (section43TimeProductSource gs).f =
          U (section43TimeProductSource gs).f) :
    T F = U F := by
  have hF :
      F ∈
        (((Submodule.span ℂ
          {G : SchwartzMap (Fin n → ℝ) ℂ |
            ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
              tsupport ((section43TimeProductSource gs).f :
                  (Fin n → ℝ) → ℂ) ⊆ Window ∧
              G = (section43TimeProductSource gs).f}) :
          Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
          Set (SchwartzMap (Fin n → ℝ) ℂ)) :=
    section43_mem_closure_productSourceSpan_of_productCutoffSupport
      χs hχ_pos hχ_compact hχ_Window F hχ_one
  exact
    section43_timeCLM_eq_of_mem_closure_supportedProductSources
      n T U hF h_on_products

/-- Local supported-product-source boundary-value extension.

If a test has already been localized into the closure of product sources
supported in a fixed window `U`, then convergence on those supported product
sources extends to that test under the Banach-Steinhaus pointwise boundedness
hypothesis.  This is the functional-analytic OS-II V.1 handoff used after
choosing a Lemma 5.1 product cutoff. -/
theorem section43_tendsto_timeSchwartz_of_mem_closure_supportedProductSources
    (n : ℕ)
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {U : Set (Fin n → ℝ)}
    {F : SchwartzMap (Fin n → ℝ) ℂ}
    (hF :
      F ∈
        (((Submodule.span ℂ
          {G : SchwartzMap (Fin n → ℝ) ℂ |
            ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
              tsupport ((section43TimeProductSource gs).f :
                  (Fin n → ℝ) → ℂ) ⊆ U ∧
              G = (section43TimeProductSource gs).f}) :
          Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
          Set (SchwartzMap (Fin n → ℝ) ℂ)))
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin n → ℝ) → ℂ) ⊆ U →
        Tendsto
          (fun a => Tseq a (section43TimeProductSource gs).f)
          l
          (nhds (T (section43TimeProductSource gs).f)))
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) φ‖ ≤ C) :
    Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  classical
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let D : Set A :=
    {G : A |
      ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
            (Fin n → ℝ) → ℂ) ⊆ U ∧
        G = (section43TimeProductSource gs).f}
  have h_onD :
      ∀ G ∈ D, Tendsto (fun a => Tseq a G) l (nhds (T G)) := by
    intro G hG
    rcases hG with ⟨gs, hgsU, rfl⟩
    exact h_on_products gs hgsU
  letI : Module ℝ A := Module.complexToReal A
  haveI : IsScalarTower ℝ ℂ A :=
    IsScalarTower.complexToReal (M := ℂ) (E := A)
  have h_equicont :
      ∀ W ∈ nhds (0 : ℂ), ∃ V ∈ nhds (0 : A),
        ∀ᶠ a in l, ∀ φ ∈ V, (Tseq a - T) φ ∈ W := by
    simpa using
      (SCV.tempered_eventually_equicontinuous_of_pointwise_bounded
        (l := l)
        (T := fun a =>
          (((Tseq a - T).restrictScalars ℝ) :
            SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ))
        (by
          intro φ
          rcases h_pointwise_bounded φ with ⟨C, hC⟩
          exact ⟨C, fun a => by simpa using hC a⟩))
  exact
    SCV.tendsto_clm_apply_of_mem_closure_span_of_eventually_equicontinuous
      (𝕜 := ℂ) (T := Tseq) (S := T) (D := D) (x := F)
      (by simpa [D, A] using hF) h_onD h_equicont

/-- Cutoff-selected local supported-product-source boundary-value extension.

If a product cutoff is one on the test support and its product support lies in
`U`, then product-source convergence on sources supported in `U` extends to
the original test.  This combines the local product-cutoff density with the
local closure Banach-Steinhaus step. -/
theorem section43_tendsto_timeSchwartz_of_productCutoff_supportedProductSources
    (n : ℕ)
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {U : Set (Fin n → ℝ)}
    (χs : Fin n → SchwartzMap ℝ ℂ)
    (hχ_pos : ∀ i : Fin n, tsupport ((χs i) : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hχ_compact : ∀ i : Fin n, HasCompactSupport ((χs i) : ℝ → ℂ))
    (hχ_U :
      ∀ τ : Fin n → ℝ,
        (∀ i : Fin n, τ i ∈ tsupport ((χs i) : ℝ → ℂ)) → τ ∈ U)
    (F : SchwartzMap (Fin n → ℝ) ℂ)
    (hχ_one :
      ∀ x ∈ tsupport (F : (Fin n → ℝ) → ℂ),
        section43TimeProductTensor χs x = 1)
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        tsupport ((section43TimeProductSource gs).f :
          (Fin n → ℝ) → ℂ) ⊆ U →
        Tendsto
          (fun a => Tseq a (section43TimeProductSource gs).f)
          l
          (nhds (T (section43TimeProductSource gs).f)))
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) φ‖ ≤ C) :
    Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  have hF :
      F ∈
        (((Submodule.span ℂ
          {G : SchwartzMap (Fin n → ℝ) ℂ |
            ∃ gs : Fin n → Section43CompactPositiveTimeSource1D,
              tsupport ((section43TimeProductSource gs).f :
                  (Fin n → ℝ) → ℂ) ⊆ U ∧
              G = (section43TimeProductSource gs).f}) :
          Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)).topologicalClosure :
          Set (SchwartzMap (Fin n → ℝ) ℂ)) :=
    section43_mem_closure_productSourceSpan_of_productCutoffSupport
      χs hχ_pos hχ_compact hχ_U F hχ_one
  exact
    section43_tendsto_timeSchwartz_of_mem_closure_supportedProductSources
      (n := n) (Tseq := Tseq) (T := T) (U := U) (F := F)
      hF h_on_products h_pointwise_bounded

/-- The finite-time compact-Laplace product generator family is closed under
complex scalar multiplication, provided there is a slot to absorb the scalar.

This is the algebraic point needed by the real-linear boundary-value extension:
the OS-II product-source limits are proved on honest one-sided product Laplace
representatives, but the local EOW theorem asks for real-linear convergence on
a dense real span. -/
theorem section43TimeProductTensor_compactLaplace_preimage_generator_smul_mem
    {n : ℕ} [Nonempty (Fin n)] (c : ℂ)
    {F : SchwartzMap (Fin n → ℝ) ℂ}
    (hF :
      F ∈
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            (∀ i : Fin n,
              fs i ∈
                section43PositiveEnergyQuotientMap1D ⁻¹'
                  Set.range section43OneSidedLaplaceCompactTransform1D) ∧
            F = section43TimeProductTensor fs}) :
    c • F ∈
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            (∀ i : Fin n,
              fs i ∈
                section43PositiveEnergyQuotientMap1D ⁻¹'
                  Set.range section43OneSidedLaplaceCompactTransform1D) ∧
            F = section43TimeProductTensor fs} := by
  classical
  rcases hF with ⟨fs, hfs, rfl⟩
  let i0 : Fin n := Classical.choice inferInstance
  let fs' : Fin n → SchwartzMap ℝ ℂ := Function.update fs i0 (c • fs i0)
  refine ⟨fs', ?_, ?_⟩
  · intro i
    by_cases hi : i = i0
    · subst hi
      rcases hfs i0 with ⟨g, hg⟩
      refine ⟨c • g, ?_⟩
      calc
        section43OneSidedLaplaceCompactTransform1D (c • g)
            = c • section43OneSidedLaplaceCompactTransform1D g := by
              rw [section43OneSidedLaplaceCompactTransform1D_map_smul]
        _ = c • section43PositiveEnergyQuotientMap1D (fs i0) := by
              rw [hg]
        _ = section43PositiveEnergyQuotientMap1D (c • fs i0) := by
              rw [map_smul]
        _ = section43PositiveEnergyQuotientMap1D (fs' i0) := by
              simp [fs']
    · simpa [fs', Function.update, hi] using hfs i
  · ext σ
    change c * (section43TimeProductTensor fs σ) =
      section43TimeProductTensor fs' σ
    rw [section43TimeProductTensor, section43TimeProductTensor,
      SchwartzMap.productTensor_apply, SchwartzMap.productTensor_apply]
    rw [show
      (fun i : Fin n => (fs' i) (σ i)) =
        Function.update (fun i : Fin n => (fs i) (σ i)) i0
          (c * (fs i0) (σ i0)) by
        funext i
        by_cases hi : i = i0
        · subst hi
          simp [fs', Function.update]
        · simp [fs', Function.update, hi]]
    rw [Finset.prod_update_of_mem (Finset.mem_univ i0)]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
      (Finset.mem_univ i0) (fun i : Fin n => (fs i) (σ i))]
    ring

/-- The real span of finite-time product tensors whose one-dimensional factors
come from compact one-sided Laplace quotient classes is dense.

The nonempty-slot assumption is exactly what lets a complex scalar be absorbed
into one product factor, converting the complex-span density theorem into the
real-linear dense span used by local EOW. -/
theorem dense_section43TimeProductTensor_real_span_compactLaplace_preimage
    (n : ℕ) [Nonempty (Fin n)] :
    Dense
      (((Submodule.span ℝ
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            (∀ i : Fin n,
              fs i ∈
                section43PositiveEnergyQuotientMap1D ⁻¹'
                  Set.range section43OneSidedLaplaceCompactTransform1D) ∧
            F = section43TimeProductTensor fs}) :
        Submodule ℝ (SchwartzMap (Fin n → ℝ) ℂ)) :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  classical
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S1 : Set (SchwartzMap ℝ ℂ) :=
    section43PositiveEnergyQuotientMap1D ⁻¹'
      Set.range section43OneSidedLaplaceCompactTransform1D
  let D : Set A :=
    {F : A | ∃ fs : Fin n → SchwartzMap ℝ ℂ,
      (∀ i : Fin n, fs i ∈ S1) ∧ F = section43TimeProductTensor fs}
  let MR : Submodule ℝ A := Submodule.span ℝ D
  have hD_complex :
      Dense (((Submodule.span ℂ D : Submodule ℂ A) : Set A)) := by
    simpa [D, S1, A] using
      section43_timeProductTensor_span_dense_of_factor_dense
        (n := n) (S := S1)
        dense_section43OneSidedLaplaceCompactTransform1D_preimage
  have hD_smul :
      ∀ (c : ℂ) ⦃F : A⦄, F ∈ D → c • F ∈ D := by
    intro c F hF
    exact
      section43TimeProductTensor_compactLaplace_preimage_generator_smul_mem
        (n := n) c hF
  have hMR_complex_smul :
      ∀ (c : ℂ) ⦃F : A⦄, F ∈ MR → c • F ∈ MR := by
    intro c F hF
    change F ∈ Submodule.span ℝ D at hF
    refine Submodule.span_induction
      (p := fun F : A => fun _ => c • F ∈ MR) ?_ ?_ ?_ ?_ hF
    · intro G hG
      exact Submodule.subset_span (hD_smul c hG)
    · simp
    · intro G H _hG _hH hGc hHc
      simpa [smul_add] using MR.add_mem hGc hHc
    · intro r G _hG hGc
      have hcomm : c • (r • G) = r • (c • G) := by
        ext σ
        change c * ((r : ℂ) * G σ) = (r : ℂ) * (c * G σ)
        ring
      rw [hcomm]
      exact MR.smul_mem r hGc
  have hcomplex_le_real :
      ((Submodule.span ℂ D : Submodule ℂ A) : Set A) ⊆ (MR : Set A) := by
    intro F hF
    change F ∈ Submodule.span ℂ D at hF
    refine Submodule.span_induction
      (p := fun F : A => fun _ => F ∈ MR) ?_ ?_ ?_ ?_ hF
    · intro G hG
      exact Submodule.subset_span hG
    · exact MR.zero_mem
    · intro G H _hG _hH hGMR hHMR
      exact MR.add_mem hGMR hHMR
    · intro c G _hG hGMR
      exact hMR_complex_smul c hGMR
  have hMR_dense : Dense (MR : Set A) :=
    Dense.mono hcomplex_le_real hD_complex
  simpa [MR, D, S1, A] using hMR_dense

/-- An integral functional whose multiplier support lies in the positive time
orthant descends to the Section 4.3 positive-time quotient.

This is the finite-time support-local part of the OS II `(5.2)` handoff: once
the cutoff support is contained in the real positive-time region, quotient
equality of the time test functions gives pointwise equality on the support of
the integral. -/
theorem section43_integralMultiplierCLM_descends_of_tsupport_positive
    (n : ℕ)
    (χ : SchwartzMap (Fin n → ℝ) ℂ)
    (H : (Fin n → ℝ) → ℂ)
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hT :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
        T φ = ∫ τ : Fin n → ℝ, (χ τ * H τ) * φ τ)
    (hχ_pos :
      tsupport (χ : (Fin n → ℝ) → ℂ) ⊆ section43TimePositiveRegion n) :
    ∀ φ ψ : SchwartzMap (Fin n → ℝ) ℂ,
      section43TimePositiveQuotientMap n φ =
        section43TimePositiveQuotientMap n ψ →
      T φ = T ψ := by
  intro φ ψ hφψ
  rw [hT φ, hT ψ]
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτχ : τ ∈ tsupport (χ : (Fin n → ℝ) → ℂ)
  · have hτpos : τ ∈ section43TimePositiveRegion n := hχ_pos hτχ
    have hφψ_point : φ τ = ψ τ :=
      eqOn_region_of_section43TimePositiveQuotientMap_eq hφψ hτpos
    simp [hφψ_point]
  · have hχ0 : χ τ = 0 := image_eq_zero_of_notMem_tsupport hτχ
    simp [hχ0]

/-- Equality on the compact one-sided Laplace product generators extends to
equality of finite-time complex Schwartz CLMs, provided both CLMs descend to the
positive-time quotient.

This is the OS II V.2 `(5.2)` same-distribution step in finite-time form:
product-source equality is first transported to every representative of the
same positive-time quotient class, then the complex density of product tensors
closes the equality on all Schwartz tests. -/
theorem section43_timeSchwartz_clm_eq_of_compactLaplace_product_sources
    (n : ℕ) [Nonempty (Fin n)]
    (T U : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        T F = T G)
    (hU_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        U F = U G)
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        T (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
        U (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    T = U := by
  classical
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S1 : Set (SchwartzMap ℝ ℂ) :=
    section43PositiveEnergyQuotientMap1D ⁻¹'
      Set.range section43OneSidedLaplaceCompactTransform1D
  let D : Set A :=
    {F : A | ∃ fs : Fin n → SchwartzMap ℝ ℂ,
      (∀ i : Fin n, fs i ∈ S1) ∧
      F = section43TimeProductTensor fs}
  have hDense :
      Dense (((Submodule.span ℂ D : Submodule ℂ A) : Set A)) := by
    simpa [D, S1, A] using
      section43_timeProductTensor_span_dense_of_factor_dense
        (n := n) (S := S1)
        dense_section43OneSidedLaplaceCompactTransform1D_preimage
  have h_onD : ∀ F ∈ D, T F = U F := by
    intro F hF
    rcases hF with ⟨fs, hfs, rfl⟩
    have hEx :
        ∀ i : Fin n,
          ∃ g : Section43CompactPositiveTimeSource1D,
            section43OneSidedLaplaceCompactTransform1D g =
              section43PositiveEnergyQuotientMap1D (fs i) := by
      intro i
      exact hfs i
    choose gs hgs using hEx
    let Fprod : A :=
      section43TimeProductTensor
        (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
    have hq :
        section43TimePositiveQuotientMap n (section43TimeProductTensor fs) =
          section43TimePositiveQuotientMap n Fprod := by
      apply section43TimePositiveQuotientMap_eq_of_eqOn_region
      intro σ hσ
      dsimp [Fprod]
      rw [section43TimeProductTensor, section43TimeProductTensor]
      rw [SchwartzMap.productTensor_apply, SchwartzMap.productTensor_apply]
      refine Finset.prod_congr rfl ?_
      intro i _hi
      have hq1 :
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
      exact eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq1 (hσ i)
    calc
      T (section43TimeProductTensor fs) = T Fprod :=
        hT_desc (section43TimeProductTensor fs) Fprod hq
      _ = U Fprod := h_on_products gs
      _ = U (section43TimeProductTensor fs) :=
        (hU_desc (section43TimeProductTensor fs) Fprod hq).symm
  apply ContinuousLinearMap.eq_of_eq_on_dense T U hDense
  intro F hF
  change F ∈ Submodule.span ℂ D at hF
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
  · intro G hG
    exact h_onD G hG
  · simp
  · intro G H _ _ hG hH
    simpa using congrArg₂ (fun a b : ℂ => a + b) hG hH
  · intro c G _ hG
    simpa using congrArg (fun z : ℂ => c * z) hG

/-- One-variable boundary-value convergence from compact one-sided Laplace
representatives.

This is the total-time version of OS II V.1 `(5.7)`--`(5.8)`: if the
regularized real-linear boundary family and its target descend to the
one-sided positive-energy quotient, compact Laplace-source convergence extends
to every one-variable Schwartz test under the Banach-Steinhaus pointwise
boundedness estimate. -/
theorem section43_tendsto_oneSided_timeSchwartz_real_of_compact_representatives_of_pointwise_bounded
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap ℝ ℂ →L[ℝ] ℂ}
    {T : SchwartzMap ℝ ℂ →L[ℝ] ℂ}
    (hTseq_desc :
      ∀ a (F G : SchwartzMap ℝ ℂ),
        section43PositiveEnergyQuotientMap1D F =
          section43PositiveEnergyQuotientMap1D G →
        Tseq a F = Tseq a G)
    (hT_desc :
      ∀ F G : SchwartzMap ℝ ℂ,
        section43PositiveEnergyQuotientMap1D F =
          section43PositiveEnergyQuotientMap1D G →
        T F = T G)
    (h_on_compact :
      ∀ g : Section43CompactPositiveTimeSource1D,
        Tendsto
          (fun a => Tseq a (section43OneSidedLaplaceSchwartzRepresentative1D g))
          l
          (nhds (T (section43OneSidedLaplaceSchwartzRepresentative1D g))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap ℝ ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) F‖ ≤ C) :
    ∀ F : SchwartzMap ℝ ℂ, Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  have h_on_preimage :
      ∀ F : SchwartzMap ℝ ℂ,
        F ∈
          (section43PositiveEnergyQuotientMap1D ⁻¹'
            Set.range section43OneSidedLaplaceCompactTransform1D) →
        Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
    intro F hF
    rcases hF with ⟨g, hg⟩
    let G : SchwartzMap ℝ ℂ :=
      section43OneSidedLaplaceSchwartzRepresentative1D g
    have hqG :
        section43PositiveEnergyQuotientMap1D G =
          section43OneSidedLaplaceCompactTransform1D g := by
      exact (section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient g).symm
    have hqFG :
        section43PositiveEnergyQuotientMap1D F =
          section43PositiveEnergyQuotientMap1D G := by
      exact hg.symm.trans hqG.symm
    have hseq :
        (fun a => Tseq a F) = fun a => Tseq a G := by
      funext a
      exact hTseq_desc a F G hqFG
    have htarget : T F = T G := hT_desc F G hqFG
    simpa [G, hseq, htarget] using h_on_compact g
  exact
    SCV.tendsto_clm_apply_of_dense_of_eventually_equicontinuous
      (hD := dense_section43OneSidedLaplaceCompactTransform1D_preimage)
      h_on_preimage
      (SCV.tempered_eventually_equicontinuous_of_pointwise_bounded
        (l := l) (T := fun a => Tseq a - T) h_pointwise_bounded)

/-- Boundary-value convergence on the compact one-sided Laplace preimage extends
to every finite time Schwartz test once the real-linear boundary family is
pointwise bounded.

This is the time-shell form of OS II V.1 `(5.7)`--`(5.8)` used by the local EOW
handoff: product-source convergence is checked on the compact Laplace
generators, and Banach-Steinhaus supplies the equicontinuity needed to pass to
all time tests. -/
theorem section43_tendsto_timeSchwartz_real_of_iteratedLaplace_generators_of_pointwise_bounded
    (n : ℕ)
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (h_on_generators :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
        F ∈
          ((section43TimePositiveQuotientMap n) ⁻¹'
            Set.range (section43IteratedLaplaceCompactTransform n)) →
          Tendsto (fun a => Tseq a F) l (nhds (T F)))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  exact
    SCV.tendsto_clm_apply_of_dense_of_eventually_equicontinuous
      (hD := dense_section43IteratedLaplaceCompactTransform_preimage n)
      h_on_generators
      (SCV.tempered_eventually_equicontinuous_of_pointwise_bounded
        (l := l) (T := fun a => Tseq a - T) h_pointwise_bounded)

/-- Boundary-value convergence from the book-level compact product-source
generators.

This is the finite-time adapter used before local EOW: if the raw boundary
family and target both descend to the positive-time quotient, then convergence
on honest products of one-sided compact Laplace representatives extends to all
finite-time Schwartz tests under the Banach-Steinhaus pointwise boundedness
estimate. -/
theorem section43_tendsto_timeSchwartz_real_of_productLaplace_generators_of_pointwise_bounded
    (n : ℕ) [Nonempty (Fin n)]
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        Tseq a F = Tseq a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        T F = T G)
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        Tendsto
          (fun a => Tseq a
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          l
          (nhds (T
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  classical
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let S1 : Set (SchwartzMap ℝ ℂ) :=
    section43PositiveEnergyQuotientMap1D ⁻¹'
      Set.range section43OneSidedLaplaceCompactTransform1D
  let D : Set A :=
    {F : A | ∃ fs : Fin n → SchwartzMap ℝ ℂ,
      (∀ i : Fin n, fs i ∈ S1) ∧ F = section43TimeProductTensor fs}
  have hD :
      Dense (((Submodule.span ℝ D : Submodule ℝ A) : Set A)) := by
    simpa [D, S1, A] using
      dense_section43TimeProductTensor_real_span_compactLaplace_preimage n
  have h_onD :
      ∀ F ∈ D, Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
    intro F hF
    rcases hF with ⟨fs, hfs, rfl⟩
    have hEx :
        ∀ i : Fin n,
          ∃ g : Section43CompactPositiveTimeSource1D,
            section43OneSidedLaplaceCompactTransform1D g =
              section43PositiveEnergyQuotientMap1D (fs i) := by
      intro i
      exact hfs i
    choose gs hgs using hEx
    let Fprod : SchwartzMap (Fin n → ℝ) ℂ :=
      section43TimeProductTensor
        (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
    have hq :
        section43TimePositiveQuotientMap n (section43TimeProductTensor fs) =
          section43TimePositiveQuotientMap n Fprod := by
      apply section43TimePositiveQuotientMap_eq_of_eqOn_region
      intro σ hσ
      dsimp [Fprod]
      rw [section43TimeProductTensor, section43TimeProductTensor]
      rw [SchwartzMap.productTensor_apply, SchwartzMap.productTensor_apply]
      refine Finset.prod_congr rfl ?_
      intro i _hi
      have hq1 :
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
      have heqOn := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq1
      exact heqOn (hσ i)
    have hlim := h_on_products gs
    have hseq :
        (fun a => Tseq a (section43TimeProductTensor fs)) =
          fun a => Tseq a Fprod := by
      funext a
      exact hTseq_desc a (section43TimeProductTensor fs) Fprod hq
    have htarget :
        T (section43TimeProductTensor fs) = T Fprod :=
      hT_desc (section43TimeProductTensor fs) Fprod hq
    simpa [hseq, htarget] using hlim
  exact
    SCV.tendsto_clm_apply_of_dense_span_of_eventually_equicontinuous
      (hD := hD) h_onD
      (SCV.tempered_eventually_equicontinuous_of_pointwise_bounded
        (l := l) (T := fun a => Tseq a - T) h_pointwise_bounded)

/-- Measurability of the product-kernel scalar current against a compact
positive-time product source.

The product kernel is only used on the compact product-source support; there
the strict-positive support condition places it in the continuity region of
`section43TimeImagAxisProductKernel`.  Outside the support the source factor
vanishes. -/
theorem section43_aestronglyMeasurable_timeProductKernel_clm_mul_productSource
    {n : ℕ}
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    AEStronglyMeasurable
      (fun ξ : Fin n → ℝ =>
        T (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
  classical
  let source : Section43CompactStrictPositiveTimeSource n :=
    section43TimeProductSource gs
  let K : Set (Fin n → ℝ) :=
    tsupport (source.f : (Fin n → ℝ) → ℂ)
  let h : (Fin n → ℝ) → ℂ :=
    fun ξ => T (section43TimeImagAxisProductKernel ξ) * source.f ξ
  have hK_comp : IsCompact K := by
    simpa [K, source] using (section43TimeProductSource gs).compact.isCompact
  have hK_meas : MeasurableSet K := hK_comp.isClosed.measurableSet
  have hkernel_cont : ContinuousOn section43TimeImagAxisProductKernel K := by
    exact
      continuousOn_section43TimeImagAxisProductKernel_strictPositive.mono
        (by
          intro ξ hξ
          simpa [K, source] using (section43TimeProductSource gs).positive hξ)
  have hscalar_cont :
      ContinuousOn
        (fun ξ : Fin n → ℝ => T (section43TimeImagAxisProductKernel ξ))
        K :=
    T.continuous.comp_continuousOn hkernel_cont
  have hsource_cont : ContinuousOn (fun ξ : Fin n → ℝ => source.f ξ) K :=
    source.f.continuous.continuousOn
  have h_cont : ContinuousOn h K := hscalar_cont.mul hsource_cont
  have hind :
      AEStronglyMeasurable (Set.indicator K h)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
    exact
      (aestronglyMeasurable_indicator_iff
        (μ := MeasureTheory.volume) (s := K) (f := h) hK_meas).2
        (h_cont.aestronglyMeasurable_of_isCompact hK_comp hK_meas)
  have heq :
      Set.indicator K h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))]
        fun ξ : Fin n → ℝ =>
          T (section43TimeImagAxisProductKernel ξ) *
            (section43TimeProductSource gs).f ξ :=
    Filter.Eventually.of_forall fun ξ => by
      by_cases hξ : ξ ∈ K
      · simp [h, K, source, Set.indicator_of_mem hξ]
      · have hzero : (source.f : SchwartzMap (Fin n → ℝ) ℂ) ξ = 0 := by
          have hzero_event :
              (source.f : (Fin n → ℝ) → ℂ) =ᶠ[𝓝 ξ] 0 :=
            notMem_tsupport_iff_eventuallyEq.mp hξ
          have hzero_set :
              {u : Fin n → ℝ |
                (source.f : SchwartzMap (Fin n → ℝ) ℂ) u = 0} ∈ 𝓝 ξ := by
            simpa using hzero_event
          exact
            (_root_.mem_of_mem_nhds
              (x := ξ)
              (s := {u : Fin n → ℝ |
                (source.f : SchwartzMap (Fin n → ℝ) ℂ) u = 0})
              hzero_set)
        simp [h, K, source, Set.indicator_of_notMem hξ, hzero]
  exact AEStronglyMeasurable.congr hind heq

set_option backward.isDefEq.respectTransparency false in
/-- Banach-Steinhaus domination for product-kernel source currents.

The compact-source bound required by dominated convergence is not an
independent OS estimate once the real-linear boundary family is pointwise
bounded: Banach-Steinhaus controls all CLM differences by one finite Schwartz
seminorm, and that seminorm is bounded on the compact image of the source
support under the imaginary-axis product kernel. -/
theorem section43_productKernel_uniform_bound_of_pointwise_bounded
    {n : ℕ} {α : Type*}
    {TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TseqR : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_apply :
      ∀ a (F : SchwartzMap (Fin n → ℝ) ℂ), TseqR a F = TseqC a F)
    (hT_apply :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, TR F = TC F)
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(TseqR a - TR) F‖ ≤ C)
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : α, ∀ ξ : Fin n → ℝ,
        ξ ∈ tsupport
          ((section43TimeProductSource gs).f : (Fin n → ℝ) → ℂ) →
        ‖TseqC a (section43TimeImagAxisProductKernel ξ)‖ ≤ C := by
  classical
  let source : Section43CompactStrictPositiveTimeSource n :=
    section43TimeProductSource gs
  let K : Set (Fin n → ℝ) :=
    tsupport (source.f : (Fin n → ℝ) → ℂ)
  letI : SMulCommClass ℝ ℝ ℂ :=
    ⟨fun a b z => by
      simp [mul_comm, mul_left_comm]⟩
  obtain ⟨s, Cnn, _hCnn_ne, hdiff_bound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := Fin n → ℝ) (F := ℂ) (G := ℂ)
      (T := fun a : α => TseqR a - TR)
      h_pointwise_bounded
  let q : Seminorm ℝ (SchwartzMap (Fin n → ℝ) ℂ) :=
    s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)
  have hws := schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ
  have hq_cont : Continuous q := by
    refine Seminorm.continuous_of_le ?_
      (show q ≤ ∑ i ∈ s, schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ i by
        simpa [q] using Seminorm.finset_sup_le_sum
          (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ) s)
    change Continuous
      (fun x => Seminorm.coeFnAddMonoidHom ℝ
        (SchwartzMap (Fin n → ℝ) ℂ)
        (∑ i ∈ s, schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ i) x)
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ => hws.continuous_seminorm i
  have hK_comp : IsCompact K := by
    simpa [K, source] using (section43TimeProductSource gs).compact.isCompact
  have hkernel_cont : ContinuousOn section43TimeImagAxisProductKernel K := by
    exact
      continuousOn_section43TimeImagAxisProductKernel_strictPositive.mono
        (by
          intro ξ hξ
          simpa [K, source] using (section43TimeProductSource gs).positive hξ)
  obtain ⟨Bq, hBq⟩ :=
    hK_comp.exists_bound_of_continuousOn
      (f := fun ξ : Fin n → ℝ => q (section43TimeImagAxisProductKernel ξ))
      (hq_cont.comp_continuousOn hkernel_cont)
  have htarget_cont :
      ContinuousOn
        (fun ξ : Fin n → ℝ => TC (section43TimeImagAxisProductKernel ξ))
        K :=
    TC.continuous.comp_continuousOn hkernel_cont
  obtain ⟨BT, hBT⟩ :=
    hK_comp.exists_bound_of_continuousOn
      (f := fun ξ : Fin n → ℝ => ‖TC (section43TimeImagAxisProductKernel ξ)‖)
      (continuous_norm.comp_continuousOn htarget_cont)
  let C : ℝ := (Cnn : ℝ) * max Bq 0 + max BT 0
  refine ⟨C, ?_, ?_⟩
  · have hCnn_nonneg : 0 ≤ (Cnn : ℝ) := by exact_mod_cast Cnn.2
    have hBq_nonneg : 0 ≤ max Bq 0 := le_max_right Bq 0
    have hBT_nonneg : 0 ≤ max BT 0 := le_max_right BT 0
    exact add_nonneg (mul_nonneg hCnn_nonneg hBq_nonneg) hBT_nonneg
  · intro a ξ hξ
    have hdiff_le :
        ‖(TseqR a - TR) (section43TimeImagAxisProductKernel ξ)‖ ≤
          (Cnn : ℝ) * q (section43TimeImagAxisProductKernel ξ) := by
      simpa [q] using hdiff_bound a (section43TimeImagAxisProductKernel ξ)
    have hq_le : q (section43TimeImagAxisProductKernel ξ) ≤ max Bq 0 := by
      have hnorm_le : ‖q (section43TimeImagAxisProductKernel ξ)‖ ≤ Bq :=
        hBq ξ (by simpa [K, source] using hξ)
      have hq_nonneg : 0 ≤ q (section43TimeImagAxisProductKernel ξ) :=
        apply_nonneg q _
      have hq_le_Bq : q (section43TimeImagAxisProductKernel ξ) ≤ Bq := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hnorm_le
      exact hq_le_Bq.trans (le_max_left Bq 0)
    have htarget_le :
        ‖TC (section43TimeImagAxisProductKernel ξ)‖ ≤ max BT 0 := by
      have hnorm := hBT ξ (by simpa [K, source] using hξ)
      simpa using hnorm.trans (le_max_left BT 0)
    have hsplit :
        TseqC a (section43TimeImagAxisProductKernel ξ) =
          (TseqR a - TR) (section43TimeImagAxisProductKernel ξ) +
            TC (section43TimeImagAxisProductKernel ξ) := by
      calc
        TseqC a (section43TimeImagAxisProductKernel ξ)
            = TseqR a (section43TimeImagAxisProductKernel ξ) := by
                exact (hTseq_apply a (section43TimeImagAxisProductKernel ξ)).symm
        _ =
            (TseqR a - TR) (section43TimeImagAxisProductKernel ξ) +
              TR (section43TimeImagAxisProductKernel ξ) := by
                simp [ContinuousLinearMap.sub_apply]
        _ =
            (TseqR a - TR) (section43TimeImagAxisProductKernel ξ) +
              TC (section43TimeImagAxisProductKernel ξ) := by
                rw [hT_apply (section43TimeImagAxisProductKernel ξ)]
    calc
      ‖TseqC a (section43TimeImagAxisProductKernel ξ)‖
          ≤ ‖(TseqR a - TR) (section43TimeImagAxisProductKernel ξ)‖ +
              ‖TC (section43TimeImagAxisProductKernel ξ)‖ := by
            rw [hsplit]
            exact norm_add_le _ _
      _ ≤ (Cnn : ℝ) * max Bq 0 + max BT 0 := by
            have hCnn_nonneg : 0 ≤ (Cnn : ℝ) := by exact_mod_cast Cnn.2
            exact add_le_add
              (hdiff_le.trans
                (mul_le_mul_of_nonneg_left hq_le hCnn_nonneg))
              htarget_le
      _ = C := rfl

/-- Dominated-convergence transport for a compact strict-positive finite-time
source.

This is the DCT step in the OS-II `(5.7)`--`(5.8)` selector argument: once the
raw positive-side scalar current converges pointwise on the imaginary-axis
kernel and is uniformly bounded on the compact source support, the convergence
passes under the compact source integral. -/
theorem section43_tendsto_integral_compact_strictPositive_source_of_eventually_uniform_bound_on_tsupport
    {n : ℕ}
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (Kseq : α → (Fin n → ℝ) → ℂ) (K : (Fin n → ℝ) → ℂ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (h_meas :
      ∀ᶠ a in l,
        AEStronglyMeasurable
          (fun t : Fin n → ℝ => Kseq a t * g.f t)
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
    (hlim : ∀ t : Fin n → ℝ,
      t ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) →
        Tendsto (fun a => Kseq a t) l (nhds (K t)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ t : Fin n → ℝ,
        t ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) → ‖Kseq a t‖ ≤ C) :
    Tendsto
      (fun a => ∫ t : Fin n → ℝ, Kseq a t * g.f t)
      l
      (nhds (∫ t : Fin n → ℝ, K t * g.f t)) := by
  classical
  rcases hbound with ⟨C, hC_nonneg, hC_bound⟩
  have hbound_integrable :
      Integrable
        (fun t : Fin n → ℝ => C * ‖(g.f : SchwartzMap (Fin n → ℝ) ℂ) t‖)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
    exact ((SchwartzMap.integrable (g.f)).norm).const_mul C
  have h_bound_event :
      ∀ᶠ a in l,
        ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)),
          ‖Kseq a t * g.f t‖ ≤
            C * ‖(g.f : SchwartzMap (Fin n → ℝ) ℂ) t‖ := by
    filter_upwards [hC_bound] with a ha
    exact Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ tsupport (g.f : (Fin n → ℝ) → ℂ)
      · calc
          ‖Kseq a t * g.f t‖ =
              ‖Kseq a t‖ * ‖(g.f : SchwartzMap (Fin n → ℝ) ℂ) t‖ := by
            rw [norm_mul]
          _ ≤ C * ‖(g.f : SchwartzMap (Fin n → ℝ) ℂ) t‖ := by
            exact mul_le_mul_of_nonneg_right (ha t ht) (norm_nonneg _)
      · have hg_zero : (g.f : SchwartzMap (Fin n → ℝ) ℂ) t = 0 :=
          image_eq_zero_of_notMem_tsupport ht
        simp [hg_zero]
  have h_lim_ae :
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)),
        Tendsto (fun a => Kseq a t * g.f t) l
          (nhds (K t * g.f t)) := by
    exact Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ tsupport (g.f : (Fin n → ℝ) → ℂ)
      · exact (hlim t ht).mul tendsto_const_nhds
      · have hg_zero : (g.f : SchwartzMap (Fin n → ℝ) ℂ) t = 0 :=
          image_eq_zero_of_notMem_tsupport ht
        simpa [hg_zero] using
          (tendsto_const_nhds :
            Tendsto (fun _a : α => (0 : ℂ)) l (nhds (0 : ℂ)))
  exact
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume)
      (F := fun a t => Kseq a t * g.f t)
      (f := fun t => K t * g.f t)
      (fun t : Fin n → ℝ => C * ‖(g.f : SchwartzMap (Fin n → ℝ) ℂ) t‖)
      h_meas h_bound_event hbound_integrable h_lim_ae

/-- Dominated-convergence transport for a compact strict-positive finite-time
source, with global pointwise convergence.  The support-restricted theorem
above is the route-correct OS-II form; this theorem preserves the older API. -/
theorem section43_tendsto_integral_compact_strictPositive_source_of_eventually_uniform_bound
    {n : ℕ}
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (Kseq : α → (Fin n → ℝ) → ℂ) (K : (Fin n → ℝ) → ℂ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (h_meas :
      ∀ᶠ a in l,
        AEStronglyMeasurable
          (fun t : Fin n → ℝ => Kseq a t * g.f t)
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
    (hlim : ∀ t : Fin n → ℝ, Tendsto (fun a => Kseq a t) l (nhds (K t)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ t : Fin n → ℝ,
        t ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) → ‖Kseq a t‖ ≤ C) :
    Tendsto
      (fun a => ∫ t : Fin n → ℝ, Kseq a t * g.f t)
      l
      (nhds (∫ t : Fin n → ℝ, K t * g.f t)) := by
  exact
    section43_tendsto_integral_compact_strictPositive_source_of_eventually_uniform_bound_on_tsupport
      Kseq K g h_meas (fun t _ht => hlim t) hbound

/-- Compact-representative transport for branch integral identities.

This is the OS-II `(5.7)`--`(5.8)` compact-source handoff in the form used by
the MZ branch family: if the moving branch integral is the raw side CLM
evaluated on the compact Laplace representative, and the limiting branch
integral is the target CLM evaluated on the same representative, then the
pointwise branch selector plus the compact real-slice bound give convergence of
the CLM values. -/
theorem section43_tendsto_iteratedLaplaceRepresentative_of_branch_integral_transport
    {n : ℕ}
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (Kseq : α → (Fin n → ℝ) → ℂ)
    (K : (Fin n → ℝ) → ℂ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (hseq_eval :
      ∀ᶠ a in l,
        TseqC a (section43IteratedLaplaceSchwartzRepresentative n g) =
          ∫ τ : Fin n → ℝ, Kseq a τ * g.f τ)
    (htarget_eval :
      TC (section43IteratedLaplaceSchwartzRepresentative n g) =
        ∫ τ : Fin n → ℝ, K τ * g.f τ)
    (hmeas :
      ∀ᶠ a in l,
        AEStronglyMeasurable
          (fun τ : Fin n → ℝ => Kseq a τ * g.f τ)
          (volume : Measure (Fin n → ℝ)))
    (hlim :
      ∀ τ : Fin n → ℝ,
        τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) →
          Tendsto (fun a => Kseq a τ) l (nhds (K τ)))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ τ : Fin n → ℝ,
        τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) → ‖Kseq a τ‖ ≤ C) :
    Tendsto
      (fun a => TseqC a (section43IteratedLaplaceSchwartzRepresentative n g))
      l
      (nhds (TC (section43IteratedLaplaceSchwartzRepresentative n g))) := by
  have hDCT :
      Tendsto
        (fun a => ∫ τ : Fin n → ℝ, Kseq a τ * g.f τ)
        l
        (nhds (∫ τ : Fin n → ℝ, K τ * g.f τ)) :=
    section43_tendsto_integral_compact_strictPositive_source_of_eventually_uniform_bound_on_tsupport
      (Kseq := Kseq) (K := K) (g := g) hmeas hlim hbound
  exact (tendsto_congr' hseq_eval).2 (by
    simpa [htarget_eval] using hDCT)

/-- Product-source selector convergence from pointwise imaginary-axis kernel
convergence.

This is the OS-II `(5.7)`--`(5.8)` bridge after the all-slots Fubini
flattening: a compact one-sided product Laplace representative is an integral
of imaginary-axis kernels against a compact positive-time source, so pointwise
selector convergence plus a uniform bound on that compact support selects the
whole product generator. -/
theorem section43_tendsto_timeProductTensor_oneSidedLaplace_of_kernel_selectors_on_tsupport
    {n : ℕ}
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (h_kernel :
      ∀ ξ : Fin n → ℝ,
        ξ ∈ tsupport
          ((section43TimeProductSource gs).f : (Fin n → ℝ) → ℂ) →
          Tendsto
            (fun a => Tseq a (section43TimeImagAxisProductKernel ξ))
            l
            (nhds (T (section43TimeImagAxisProductKernel ξ))))
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ ξ : Fin n → ℝ,
        ξ ∈ tsupport
          ((section43TimeProductSource gs).f : (Fin n → ℝ) → ℂ) →
        ‖Tseq a (section43TimeImagAxisProductKernel ξ)‖ ≤ C) :
    Tendsto
      (fun a =>
        Tseq a
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
      l
      (nhds
        (T
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) := by
  classical
  let Fprod : SchwartzMap (Fin n → ℝ) ℂ :=
    section43TimeProductTensor
      (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
  have hflat_seq :
      ∀ a : α,
        Tseq a Fprod =
          ∫ ξ : Fin n → ℝ,
            Tseq a (section43TimeImagAxisProductKernel ξ) *
              (section43TimeProductSource gs).f ξ := by
    intro a
    simpa [Fprod] using
      (section43TimeProductTensor_allSlots_flattened (Tseq a) gs (fun _ => 0))
  have hflat_target :
      T Fprod =
        ∫ ξ : Fin n → ℝ,
          T (section43TimeImagAxisProductKernel ξ) *
            (section43TimeProductSource gs).f ξ := by
    simpa [Fprod] using
      (section43TimeProductTensor_allSlots_flattened T gs (fun _ => 0))
  have hdct :
      Tendsto
        (fun a =>
          ∫ ξ : Fin n → ℝ,
            Tseq a (section43TimeImagAxisProductKernel ξ) *
              (section43TimeProductSource gs).f ξ)
        l
        (nhds
          (∫ ξ : Fin n → ℝ,
            T (section43TimeImagAxisProductKernel ξ) *
              (section43TimeProductSource gs).f ξ)) :=
    have h_meas :
        ∀ᶠ a in l,
          AEStronglyMeasurable
            (fun ξ : Fin n → ℝ =>
              Tseq a (section43TimeImagAxisProductKernel ξ) *
                (section43TimeProductSource gs).f ξ)
            (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) :=
      Filter.Eventually.of_forall fun a =>
        section43_aestronglyMeasurable_timeProductKernel_clm_mul_productSource
          (Tseq a) gs
    section43_tendsto_integral_compact_strictPositive_source_of_eventually_uniform_bound_on_tsupport
      (Kseq := fun a ξ => Tseq a (section43TimeImagAxisProductKernel ξ))
      (K := fun ξ => T (section43TimeImagAxisProductKernel ξ))
      (g := section43TimeProductSource gs)
      h_meas h_kernel h_bound
  have hfun :
      (fun a => Tseq a Fprod) =
        fun a =>
          ∫ ξ : Fin n → ℝ,
            Tseq a (section43TimeImagAxisProductKernel ξ) *
              (section43TimeProductSource gs).f ξ := by
    funext a
    exact hflat_seq a
  simpa [Fprod, hfun, hflat_target] using hdct

/-- Product-source selector convergence from global pointwise imaginary-axis
kernel convergence.  The support-restricted theorem above is the OS-II-facing
form; this theorem preserves the older API. -/
theorem section43_tendsto_timeProductTensor_oneSidedLaplace_of_kernel_selectors
    {n : ℕ}
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (h_kernel :
      ∀ ξ : Fin n → ℝ,
        Tendsto
          (fun a => Tseq a (section43TimeImagAxisProductKernel ξ))
          l
          (nhds (T (section43TimeImagAxisProductKernel ξ))))
    (h_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a in l, ∀ ξ : Fin n → ℝ,
        ξ ∈ tsupport
          ((section43TimeProductSource gs).f : (Fin n → ℝ) → ℂ) →
        ‖Tseq a (section43TimeImagAxisProductKernel ξ)‖ ≤ C) :
    Tendsto
      (fun a =>
        Tseq a
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
      l
      (nhds
        (T
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) := by
  exact
    section43_tendsto_timeProductTensor_oneSidedLaplace_of_kernel_selectors_on_tsupport
      Tseq T gs (fun ξ _hξ => h_kernel ξ) h_bound

/-- All-test finite-time boundary convergence from product-kernel selectors.

This is the local-EOW-facing form of OS-II `(5.7)`--`(5.8)`: pointwise
selection on the imaginary-axis product kernels gives compact product-source
generator convergence by dominated convergence, and the product-Laplace density
plus Banach-Steinhaus extends that limit to every finite-time Schwartz test. -/
theorem section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
    (n : ℕ) [Nonempty (Fin n)]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] [NeBot l]
    {TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TseqR : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_apply :
      ∀ a (F : SchwartzMap (Fin n → ℝ) ℂ), TseqR a F = TseqC a F)
    (hT_apply :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, TR F = TC F)
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TseqR a F = TseqR a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TR F = TR G)
    (h_kernel :
      ∀ ξ : Fin n → ℝ,
        ξ ∈ section43TimeStrictPositiveRegion n →
        Tendsto
          (fun a => TseqC a (section43TimeImagAxisProductKernel ξ))
          l
          (nhds (TC (section43TimeImagAxisProductKernel ξ))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(TseqR a - TR) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => TseqR a F) l (nhds (TR F)) := by
  classical
  have h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        Tendsto
          (fun a => TseqR a
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          l
          (nhds (TR
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) := by
    intro gs
    let Fprod : SchwartzMap (Fin n → ℝ) ℂ :=
      section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
    have hprodC :
        Tendsto
          (fun a => TseqC a Fprod)
          l
          (nhds (TC Fprod)) := by
      have h_bound :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ a in l, ∀ ξ : Fin n → ℝ,
              ξ ∈ tsupport
                ((section43TimeProductSource gs).f : (Fin n → ℝ) → ℂ) →
              ‖TseqC a (section43TimeImagAxisProductKernel ξ)‖ ≤ C := by
        rcases
          section43_productKernel_uniform_bound_of_pointwise_bounded
            (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
            hTseq_apply hT_apply h_pointwise_bounded gs with
          ⟨C, hC_nonneg, hC_bound⟩
        exact ⟨C, hC_nonneg, Filter.Eventually.of_forall hC_bound⟩
      simpa [Fprod] using
        section43_tendsto_timeProductTensor_oneSidedLaplace_of_kernel_selectors_on_tsupport
          (Tseq := TseqC) (T := TC) gs
          (fun ξ hξ => h_kernel ξ ((section43TimeProductSource gs).positive hξ))
          h_bound
    have hseq :
        (fun a => TseqR a Fprod) = fun a => TseqC a Fprod := by
      funext a
      exact hTseq_apply a Fprod
    have htarget : TR Fprod = TC Fprod := hT_apply Fprod
    simpa [Fprod, hseq, htarget] using hprodC
  have h_all_real :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
        Tendsto (fun a => TseqR a F) l (nhds (TR F)) :=
    section43_tendsto_timeSchwartz_real_of_productLaplace_generators_of_pointwise_bounded
      (n := n) (Tseq := TseqR) (T := TR)
      hTseq_desc hT_desc h_on_products h_pointwise_bounded
  intro F
  exact h_all_real F

/-- Integral boundary-value convergence from product-Laplace generator limits.

This is the direct OS-II V.1 `(5.7)`--`(5.8)` density lift after a concrete
finite-height source-current calculation: convergence is supplied on products
of one-sided compact Laplace representatives, quotient descent and
Banach-Steinhaus extend it to all finite-time Schwartz tests, and the explicit
branch integral representation converts the CLM limit into the local-EOW
boundary-value limit. -/
theorem section43_tendsto_localEOW_boundary_integral_of_productLaplace_generators
    (n : ℕ) [Nonempty (Fin n)]
    {Cplus E : Set (Fin n → ℝ)}
    {Fplus : (Fin n → ℂ) → ℂ}
    [NeBot (𝓝[Cplus] (0 : Fin n → ℝ))]
    (TseqC : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TseqR : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (hTseq_apply :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ), TseqR y φ = TseqC y φ)
    (hT_apply :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, TR φ = TC φ)
    (hTseq_desc :
      ∀ y (φ ψ : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TseqR y φ = TseqR y ψ)
    (hT_desc :
      ∀ φ ψ : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TR φ = TR ψ)
    (h_on_products :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        Tendsto
          (fun y : Fin n → ℝ =>
            TseqC y
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          (𝓝[Cplus] (0 : Fin n → ℝ))
          (nhds
            (TC
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))))
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin n → ℝ, ‖(TseqR y - TR) φ‖ ≤ C)
    (h_integral :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ),
        HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
        tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        TseqR y φ =
          ∫ x : Fin n → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x) :
    ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        Tendsto
          (fun y : Fin n → ℝ =>
            ∫ x : Fin n → ℝ,
              Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
                φ x)
          (𝓝[Cplus] (0 : Fin n → ℝ))
          (nhds (TR φ)) := by
  intro φ hφ_compact hφ_support
  let l : Filter (Fin n → ℝ) := 𝓝[Cplus] (0 : Fin n → ℝ)
  have h_on_productsR :
      ∀ gs : Fin n → Section43CompactPositiveTimeSource1D,
        Tendsto
          (fun y : Fin n → ℝ =>
            TseqR y
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
          l
          (nhds
            (TR
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) := by
    intro gs
    let Fprod : SchwartzMap (Fin n → ℝ) ℂ :=
      section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))
    have hseq :
        (fun y : Fin n → ℝ => TseqR y Fprod) =
          fun y : Fin n → ℝ => TseqC y Fprod := by
      funext y
      exact hTseq_apply y Fprod
    have htarget : TR Fprod = TC Fprod := hT_apply Fprod
    simpa [l, Fprod, hseq, htarget] using h_on_products gs
  have h_all :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
        Tendsto (fun y : Fin n → ℝ => TseqR y φ) l (nhds (TR φ)) := by
    exact
      section43_tendsto_timeSchwartz_real_of_productLaplace_generators_of_pointwise_bounded
        (n := n) (Tseq := TseqR) (T := TR)
        hTseq_desc hT_desc h_on_productsR h_pointwise_bounded
  have h_event :
      (fun y : Fin n → ℝ =>
        ∫ x : Fin n → ℝ,
          Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
            φ x)
        =ᶠ[l] fun y : Fin n → ℝ => TseqR y φ := by
    exact Filter.Eventually.of_forall fun y =>
      (h_integral y φ hφ_compact hφ_support).symm
  exact (tendsto_congr' h_event).2 (h_all φ)

/-- Integral boundary-value form of
`section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded`.

This is the local-EOW-facing OS-II `(5.7)`--`(5.8)` handoff: after the
Section 4.3 selector theorem proves convergence of the raw real-linear CLMs on
all time Schwartz tests, an explicit integral representation of those CLMs
gives the boundary-value limit for the side branch itself. -/
theorem section43_tendsto_localEOW_boundary_integral_of_productKernel_selectors
    (n : ℕ) [Nonempty (Fin n)]
    {Cplus E : Set (Fin n → ℝ)}
    {Fplus : (Fin n → ℂ) → ℂ}
    [NeBot (𝓝[Cplus] (0 : Fin n → ℝ))]
    (TseqC : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TseqR : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (hTseq_apply :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ), TseqR y φ = TseqC y φ)
    (hT_apply :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, TR φ = TC φ)
    (hTseq_desc :
      ∀ y (φ ψ : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TseqR y φ = TseqR y ψ)
    (hT_desc :
      ∀ φ ψ : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TR φ = TR ψ)
    (h_kernel :
      ∀ ξ : Fin n → ℝ,
        ξ ∈ section43TimeStrictPositiveRegion n →
        Tendsto
          (fun y : Fin n → ℝ =>
            TseqC y (section43TimeImagAxisProductKernel ξ))
          (𝓝[Cplus] (0 : Fin n → ℝ))
          (nhds (TC (section43TimeImagAxisProductKernel ξ))))
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin n → ℝ, ‖(TseqR y - TR) φ‖ ≤ C)
    (h_integral :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ),
        HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
        tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        TseqR y φ =
          ∫ x : Fin n → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x) :
    ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        Tendsto
          (fun y : Fin n → ℝ =>
            ∫ x : Fin n → ℝ,
              Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
                φ x)
          (𝓝[Cplus] (0 : Fin n → ℝ))
          (nhds (TR φ)) := by
  intro φ hφ_compact hφ_support
  let l : Filter (Fin n → ℝ) := 𝓝[Cplus] (0 : Fin n → ℝ)
  have hl_cg : l.IsCountablyGenerated := by infer_instance
  have hl_neBot : NeBot l := by infer_instance
  have h_all :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
        Tendsto (fun y : Fin n → ℝ => TseqR y φ) l (nhds (TR φ)) := by
    letI : l.IsCountablyGenerated := hl_cg
    letI : NeBot l := hl_neBot
    exact
      section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
        (n := n) (l := l)
        (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
        hTseq_apply hT_apply hTseq_desc hT_desc
        (by
          intro ξ hξ
          simpa [l] using h_kernel ξ hξ)
        h_pointwise_bounded
  have h_event :
      (fun y : Fin n → ℝ =>
        ∫ x : Fin n → ℝ,
          Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
            φ x)
        =ᶠ[l] fun y : Fin n → ℝ => TseqR y φ := by
    exact Filter.Eventually.of_forall fun y =>
      (h_integral y φ hφ_compact hφ_support).symm
  exact (tendsto_congr' h_event).2 (h_all φ)

/-- All-test finite-time boundary convergence from global product-kernel
selectors.  The strict-positive version above is the route-correct OS-II
surface; this theorem preserves the older API. -/
theorem section43_tendsto_timeSchwartz_real_of_productKernel_selectors_of_pointwise_bounded
    (n : ℕ) [Nonempty (Fin n)]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] [NeBot l]
    {TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TseqR : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_apply :
      ∀ a (F : SchwartzMap (Fin n → ℝ) ℂ), TseqR a F = TseqC a F)
    (hT_apply :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, TR F = TC F)
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TseqR a F = TseqR a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TR F = TR G)
    (h_kernel :
      ∀ ξ : Fin n → ℝ,
        Tendsto
          (fun a => TseqC a (section43TimeImagAxisProductKernel ξ))
          l
          (nhds (TC (section43TimeImagAxisProductKernel ξ))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(TseqR a - TR) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => TseqR a F) l (nhds (TR F)) := by
  exact
    section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
      n hTseq_apply hT_apply hTseq_desc hT_desc
      (fun ξ _hξ => h_kernel ξ) h_pointwise_bounded

/-- Transport compact-source boundary convergence to every representative of the
same positive-time quotient.

The raw OS-II `(5.7)`--`(5.8)` identities are proved on explicit compact
Laplace representatives.  The dense boundary theorem quantifies over every time
Schwartz test whose positive-time quotient lies in the compact-transform range.
This lemma performs that representative-change step under explicit descent
hypotheses for the boundary family and its target. -/
theorem section43_timeSchwartz_generator_limit_of_compact_representatives
    (n : ℕ)
    {α : Type*} {l : Filter α}
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        Tseq a F = Tseq a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        T F = T G)
    (h_on_compact :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        Tendsto
          (fun a => Tseq a (section43IteratedLaplaceSchwartzRepresentative n g))
          l
          (nhds (T (section43IteratedLaplaceSchwartzRepresentative n g)))) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      F ∈
        ((section43TimePositiveQuotientMap n) ⁻¹'
          Set.range (section43IteratedLaplaceCompactTransform n)) →
      Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  intro F hF
  rcases hF with ⟨g, hg⟩
  let G : SchwartzMap (Fin n → ℝ) ℂ :=
    section43IteratedLaplaceSchwartzRepresentative n g
  have hG_rep : section43IteratedLaplaceRepresentative n g G := by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
  have hqG :
      section43TimePositiveQuotientMap n G =
        section43IteratedLaplaceCompactTransform n g := by
    exact (section43IteratedLaplaceCompactTransform_eq_quotient n g G hG_rep).symm
  have hqFG :
      section43TimePositiveQuotientMap n F =
        section43TimePositiveQuotientMap n G := by
    exact hg.symm.trans hqG.symm
  have hseq :
      (fun a => Tseq a F) =ᶠ[l] fun a => Tseq a G := by
    exact Filter.Eventually.of_forall fun a => hTseq_desc a F G hqFG
  have htarget : T F = T G := hT_desc F G hqFG
  exact (tendsto_congr' hseq).2 (by simpa [G, htarget] using h_on_compact g)

/-- All-test finite-time boundary convergence from compact multitime Laplace
representatives.

This is the direct OS-II `(5.7)`--`(5.8)` dense-boundary handoff in the
iterated compact-source form: after quotient descent, convergence on the
actual compact Laplace representatives is enough to give convergence on the
dense generator class; Banach-Steinhaus pointwise boundedness then extends the
limit to every finite-time Schwartz test. -/
theorem section43_tendsto_timeSchwartz_real_of_compact_representatives_of_pointwise_bounded
    (n : ℕ)
    {α : Type*} {l : Filter α} [NeBot l]
    {Tseq : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {T : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        Tseq a F = Tseq a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        T F = T G)
    (h_on_compact :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        Tendsto
          (fun a => Tseq a (section43IteratedLaplaceSchwartzRepresentative n g))
          l
          (nhds (T (section43IteratedLaplaceSchwartzRepresentative n g))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(Tseq a - T) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => Tseq a F) l (nhds (T F)) := by
  exact
    section43_tendsto_timeSchwartz_real_of_iteratedLaplace_generators_of_pointwise_bounded
      n
      (section43_timeSchwartz_generator_limit_of_compact_representatives
        (n := n) (Tseq := Tseq) (T := T)
        hTseq_desc hT_desc h_on_compact)
      h_pointwise_bounded

/-- Complex-linear compact-representative boundary convergence transported to
the real-linear local-EOW interface.

The raw OS-II branch family is usually built as complex-linear functionals, but
the regularized local EOW theorem is stated over real-linear Schwartz tests.
This theorem performs only that scalar-interface change after the genuine
inputs have been proved: quotient descent, compact Laplace-representative
convergence, and Banach-Steinhaus pointwise boundedness. -/
theorem section43_tendsto_timeSchwartz_real_of_complex_compact_representatives_of_pointwise_bounded
    (n : ℕ)
    {α : Type*} {l : Filter α} [NeBot l]
    {TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TseqR : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (hTseq_apply :
      ∀ a (F : SchwartzMap (Fin n → ℝ) ℂ), TseqR a F = TseqC a F)
    (hT_apply :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, TR F = TC F)
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TseqR a F = TseqR a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TR F = TR G)
    (h_on_compact :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        Tendsto
          (fun a => TseqC a (section43IteratedLaplaceSchwartzRepresentative n g))
          l
          (nhds (TC (section43IteratedLaplaceSchwartzRepresentative n g))))
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(TseqR a - TR) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => TseqR a F) l (nhds (TR F)) := by
  have h_on_compactR :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        Tendsto
          (fun a => TseqR a (section43IteratedLaplaceSchwartzRepresentative n g))
          l
          (nhds (TR (section43IteratedLaplaceSchwartzRepresentative n g))) := by
    intro g
    let Φ : SchwartzMap (Fin n → ℝ) ℂ :=
      section43IteratedLaplaceSchwartzRepresentative n g
    have hseq :
        (fun a => TseqR a Φ) = fun a => TseqC a Φ := by
      funext a
      exact hTseq_apply a Φ
    have htarget : TR Φ = TC Φ := hT_apply Φ
    simpa [Φ, hseq, htarget] using h_on_compact g
  exact
    section43_tendsto_timeSchwartz_real_of_compact_representatives_of_pointwise_bounded
      n hTseq_desc hT_desc h_on_compactR h_pointwise_bounded

/-- All-test finite-time boundary convergence from compact branch-integral
identities.

This is the route-facing OS-II V.1 `(5.7)`--`(5.8)` adapter.  The hypotheses
are the concrete branch-side inputs still to be supplied by the MZ/semigroup
family: moving CLM values equal compact branch integrals, target CLM values
equal the limiting branch integrals, pointwise branch selectors converge on
each compact real support, and the same branch family is bounded there.  The
conclusion is the real-linear all-test convergence consumed by fixed-window
local EOW. -/
theorem section43_tendsto_timeSchwartz_real_of_branch_integral_compact_representatives
    (n : ℕ)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated] [NeBot l]
    {TseqC : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ}
    {TseqR : α → SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    {TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ}
    (Kseq : α → (Fin n → ℝ) → ℂ)
    (K : (Fin n → ℝ) → ℂ)
    (hTseq_apply :
      ∀ a (F : SchwartzMap (Fin n → ℝ) ℂ), TseqR a F = TseqC a F)
    (hT_apply :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, TR F = TC F)
    (hTseq_desc :
      ∀ a (F G : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TseqR a F = TseqR a G)
    (hT_desc :
      ∀ F G : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n F =
          section43TimePositiveQuotientMap n G →
        TR F = TR G)
    (hseq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ᶠ a in l,
          TseqC a (section43IteratedLaplaceSchwartzRepresentative n g) =
            ∫ τ : Fin n → ℝ, Kseq a τ * g.f τ)
    (htarget_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        TC (section43IteratedLaplaceSchwartzRepresentative n g) =
          ∫ τ : Fin n → ℝ, K τ * g.f τ)
    (hmeas :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ᶠ a in l,
          AEStronglyMeasurable
            (fun τ : Fin n → ℝ => Kseq a τ * g.f τ)
            (volume : Measure (Fin n → ℝ)))
    (hlim :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ τ : Fin n → ℝ,
          τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) →
            Tendsto (fun a => Kseq a τ) l (nhds (K τ)))
    (hbound_compact : ∀ g : Section43CompactStrictPositiveTimeSource n,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ a in l, ∀ τ : Fin n → ℝ,
          τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) → ‖Kseq a τ‖ ≤ C)
    (h_pointwise_bounded :
      ∀ F : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ a : α, ‖(TseqR a - TR) F‖ ≤ C) :
    ∀ F : SchwartzMap (Fin n → ℝ) ℂ,
      Tendsto (fun a => TseqR a F) l (nhds (TR F)) := by
  refine
    section43_tendsto_timeSchwartz_real_of_complex_compact_representatives_of_pointwise_bounded
      (n := n) (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
      hTseq_apply hT_apply hTseq_desc hT_desc ?_ h_pointwise_bounded
  intro g
  exact
    section43_tendsto_iteratedLaplaceRepresentative_of_branch_integral_transport
      (TseqC := TseqC) (TC := TC) (Kseq := Kseq) (K := K) (g := g)
      (hseq_eval g) (htarget_eval g) (hmeas g) (hlim g)
      (hbound_compact g)

/-- Integral local-EOW boundary values from compact branch-integral identities.

This is the local-EOW-facing form of the compact OS-II V.1 `(5.7)`--`(5.8)`
handoff.  The concrete branch family must still supply the genuine
source-current identities:

* moving side CLM values equal compact branch integrals,
* target CLM values equal limiting branch integrals,
* pointwise branch selection and compact real-slice bounds.

Once those are available, quotient descent and Banach-Steinhaus give all-test
CLM convergence, and the explicit side integral representation turns that into
the raw boundary-value hypothesis consumed by local EOW. -/
theorem section43_tendsto_localEOW_boundary_integral_of_branch_integral_compact_representatives
    (n : ℕ) [Nonempty (Fin n)]
    {Cplus E : Set (Fin n → ℝ)}
    {Fplus : (Fin n → ℂ) → ℂ}
    [NeBot (𝓝[Cplus] (0 : Fin n → ℝ))]
    (TseqC : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TC : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (TseqR : (Fin n → ℝ) →
      SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (TR : SchwartzMap (Fin n → ℝ) ℂ →L[ℝ] ℂ)
    (Kseq : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (K : (Fin n → ℝ) → ℂ)
    (hTseq_apply :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ), TseqR y φ = TseqC y φ)
    (hT_apply :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, TR φ = TC φ)
    (hTseq_desc :
      ∀ y (φ ψ : SchwartzMap (Fin n → ℝ) ℂ),
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TseqR y φ = TseqR y ψ)
    (hT_desc :
      ∀ φ ψ : SchwartzMap (Fin n → ℝ) ℂ,
        section43TimePositiveQuotientMap n φ =
          section43TimePositiveQuotientMap n ψ →
        TR φ = TR ψ)
    (hseq_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin n → ℝ),
          TseqC y (section43IteratedLaplaceSchwartzRepresentative n g) =
            ∫ τ : Fin n → ℝ, Kseq y τ * g.f τ)
    (htarget_eval :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        TC (section43IteratedLaplaceSchwartzRepresentative n g) =
          ∫ τ : Fin n → ℝ, K τ * g.f τ)
    (hmeas :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin n → ℝ),
          AEStronglyMeasurable
            (fun τ : Fin n → ℝ => Kseq y τ * g.f τ)
            (volume : Measure (Fin n → ℝ)))
    (hlim :
      ∀ g : Section43CompactStrictPositiveTimeSource n,
        ∀ τ : Fin n → ℝ,
          τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) →
            Tendsto (fun y : Fin n → ℝ => Kseq y τ)
              (𝓝[Cplus] (0 : Fin n → ℝ)) (nhds (K τ)))
    (hbound_compact : ∀ g : Section43CompactStrictPositiveTimeSource n,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ y in 𝓝[Cplus] (0 : Fin n → ℝ), ∀ τ : Fin n → ℝ,
          τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ) → ‖Kseq y τ‖ ≤ C)
    (h_pointwise_bounded :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ, ∃ C : ℝ,
        ∀ y : Fin n → ℝ, ‖(TseqR y - TR) φ‖ ≤ C)
    (h_integral :
      ∀ y (φ : SchwartzMap (Fin n → ℝ) ℂ),
        HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
        tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        TseqR y φ =
          ∫ x : Fin n → ℝ,
            Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
              φ x) :
    ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      HasCompactSupport (φ : (Fin n → ℝ) → ℂ) →
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ E →
        Tendsto
          (fun y : Fin n → ℝ =>
            ∫ x : Fin n → ℝ,
              Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
                φ x)
          (𝓝[Cplus] (0 : Fin n → ℝ))
          (nhds (TR φ)) := by
  intro φ hφ_compact hφ_support
  let l : Filter (Fin n → ℝ) := 𝓝[Cplus] (0 : Fin n → ℝ)
  have hl_cg : l.IsCountablyGenerated := by infer_instance
  have hl_neBot : NeBot l := by infer_instance
  have h_all :
      ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
        Tendsto (fun y : Fin n → ℝ => TseqR y φ) l (nhds (TR φ)) := by
    letI : l.IsCountablyGenerated := hl_cg
    letI : NeBot l := hl_neBot
    exact
      section43_tendsto_timeSchwartz_real_of_branch_integral_compact_representatives
        (n := n) (l := l)
        (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
        Kseq K hTseq_apply hT_apply hTseq_desc hT_desc
        (by
          intro g
          simpa [l] using hseq_eval g)
        htarget_eval
        (by
          intro g
          simpa [l] using hmeas g)
        (by
          intro g τ hτ
          simpa [l] using hlim g τ hτ)
        (by
          intro g
          rcases hbound_compact g with ⟨C, hC, hC_bound⟩
          refine ⟨C, hC, ?_⟩
          simpa [l] using hC_bound)
        h_pointwise_bounded
  have h_event :
      (fun y : Fin n → ℝ =>
        ∫ x : Fin n → ℝ,
          Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) * Complex.I) *
            φ x)
        =ᶠ[l] fun y : Fin n → ℝ => TseqR y φ := by
    exact Filter.Eventually.of_forall fun y =>
      (h_integral y φ hφ_compact hφ_support).symm
  exact (tendsto_congr' h_event).2 (h_all φ)

end OSReconstruction
