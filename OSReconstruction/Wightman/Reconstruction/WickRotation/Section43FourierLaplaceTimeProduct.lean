import Mathlib.MeasureTheory.Integral.Pi
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceFiniteProbe

/-!
# Section 4.3 finite time-product density support

This file starts the finite-time product layer of the Section 4.3 OS-route
density theorem.  It keeps the multitime quotient/source surface separate from
the already-large one-variable and finite-probe files.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Closed positive orthant in the finite Euclidean time variables. -/
def section43TimePositiveRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {τ | ∀ i : Fin n, 0 ≤ τ i}

/-- Strict positive orthant in the finite Euclidean time variables. -/
def section43TimeStrictPositiveRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {τ | ∀ i : Fin n, 0 < τ i}

/-- The one-sided collar around the finite-time positive orthant. -/
def section43TimePositiveThickening (n : ℕ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {τ | ∀ i : Fin n, -ε ≤ τ i}

/-- Product cutoff for the finite-time positive orthant.  It is one on the
closed positive orthant and vanishes once any coordinate is at most `-1`. -/
noncomputable def section43TimePositiveCutoff (n : ℕ) :
    (Fin n → ℝ) → ℂ :=
  fun τ => ∏ i : Fin n, (SCV.smoothCutoff (τ i) : ℂ)

/-- The finite-time positive cutoff is exactly `1` on the closed positive
orthant. -/
theorem section43TimePositiveCutoff_eq_one_of_mem
    {n : ℕ} {τ : Fin n → ℝ}
    (hτ : τ ∈ section43TimePositiveRegion n) :
    section43TimePositiveCutoff n τ = 1 := by
  rw [section43TimePositiveCutoff]
  apply Finset.prod_eq_one
  intro i _hi
  have hi : 0 ≤ τ i := hτ i
  rw [SCV.smoothCutoff_one_of_nonneg hi]
  simp

/-- The finite-time positive cutoff vanishes when one coordinate lies at or
below `-1`. -/
theorem section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
    {n : ℕ} {τ : Fin n → ℝ} {i : Fin n}
    (hi : τ i ≤ -1) :
    section43TimePositiveCutoff n τ = 0 := by
  rw [section43TimePositiveCutoff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by
    rw [SCV.smoothCutoff_zero_of_le_neg_one hi]
    simp)

/-- The finite-time positive cutoff vanishes outside the unit one-sided
collar. -/
theorem section43TimePositiveCutoff_eq_zero_of_not_mem_thickening_one
    {n : ℕ} {τ : Fin n → ℝ}
    (hτ : τ ∉ section43TimePositiveThickening n 1) :
    section43TimePositiveCutoff n τ = 0 := by
  rw [section43TimePositiveThickening] at hτ
  rcases not_forall.mp hτ with ⟨i, hi_not⟩
  have hi : τ i < -1 := not_le.mp hi_not
  exact section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
    (n := n) (τ := τ) (i := i) (le_of_lt hi)

/-- The finite-time product cutoff is ambient smooth. -/
theorem section43TimePositiveCutoff_contDiff
    (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43TimePositiveCutoff n) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun τ : Fin n → ℝ => ∏ i : Fin n, (SCV.smoothCutoff (τ i) : ℂ))
  apply contDiff_prod
  intro i _hi
  have hcoord :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : Fin n → ℝ => τ i) := by
    simpa using
      ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) i).contDiff :
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : Fin n → ℝ =>
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
            (φ := fun _ => ℝ) i) τ))
  exact Complex.ofRealCLM.contDiff.comp (SCV.smoothCutoff_contDiff.comp hcoord)

/-- The finite-time product cutoff has temperate growth. -/
theorem section43TimePositiveCutoff_hasTemperateGrowth
    (n : ℕ) :
    Function.HasTemperateGrowth (section43TimePositiveCutoff n) := by
  classical
  change Function.HasTemperateGrowth
    (fun τ : Fin n → ℝ => ∏ i : Fin n, (SCV.smoothCutoff (τ i) : ℂ))
  let factor : Fin n → (Fin n → ℝ) → ℂ := fun i τ =>
    (SCV.smoothCutoff (τ i) : ℂ)
  have hfactor : ∀ i : Fin n, Function.HasTemperateGrowth (factor i) := by
    intro i
    have hcoord : Function.HasTemperateGrowth (fun τ : Fin n → ℝ => τ i) := by
      simpa using
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
          (φ := fun _ => ℝ) i).hasTemperateGrowth :
          Function.HasTemperateGrowth (fun τ : Fin n → ℝ =>
            (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
              (φ := fun _ => ℝ) i) τ))
    simpa [factor, Function.comp_def] using
      SCV.smoothCutoff_complex_hasTemperateGrowth.comp hcoord
  have hprod : Function.HasTemperateGrowth
      (fun τ : Fin n → ℝ => ∏ i : Fin n, factor i τ) := by
    let P : Finset (Fin n) → Prop := fun s =>
      Function.HasTemperateGrowth
        (fun τ : Fin n → ℝ => ∏ i ∈ s, factor i τ)
    change P Finset.univ
    refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?empty ?insert
    · simp [P, Function.HasTemperateGrowth.const]
    · intro a s has ih
      have ha : Function.HasTemperateGrowth (factor a) := hfactor a
      have hs : Function.HasTemperateGrowth
          (fun τ : Fin n → ℝ => ∏ i ∈ s, factor i τ) := ih
      simpa [P, Finset.prod_insert has] using ha.mul hs
  simpa [factor] using hprod

/-- Every derivative of the finite-time product cutoff vanishes outside the
unit one-sided collar. -/
theorem section43TimePositiveCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
    {n r : ℕ} {τ : Fin n → ℝ}
    (hτ : τ ∉ section43TimePositiveThickening n 1) :
    iteratedFDeriv ℝ r (section43TimePositiveCutoff n) τ = 0 := by
  rw [section43TimePositiveThickening] at hτ
  rcases not_forall.mp hτ with ⟨i, hi_not⟩
  have hi : τ i < -1 := not_le.mp hi_not
  have hcoord_cont : Continuous fun τ' : Fin n → ℝ => τ' i :=
    continuous_apply i
  have hlt_event : ∀ᶠ τ' in 𝓝 τ, τ' i < -1 :=
    (isOpen_lt hcoord_cont continuous_const).mem_nhds hi
  have hzero_event : section43TimePositiveCutoff n =ᶠ[𝓝 τ] 0 := by
    filter_upwards [hlt_event] with τ' hτ'
    exact section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
      (n := n) (τ := τ') (i := i) (le_of_lt hτ')
  exact iteratedFDeriv_eq_zero_of_eventuallyEq_zero hzero_event r

/-- The support of every derivative of the finite-time positive cutoff is
contained in the unit one-sided collar. -/
theorem section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
    (n r : ℕ) :
    ∀ τ : Fin n → ℝ,
      iteratedFDeriv ℝ r (section43TimePositiveCutoff n) τ ≠ 0 →
        τ ∈ section43TimePositiveThickening n 1 := by
  intro τ hτ_nonzero
  by_contra hτ
  exact hτ_nonzero
    (section43TimePositiveCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
      (n := n) (r := r) (τ := τ) hτ)

/-- Time-Schwartz tests that vanish on the closed positive orthant. -/
def section43TimeVanishingSubmodule (n : ℕ) :
    Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ) where
  carrier := {f |
    Set.EqOn (f : (Fin n → ℝ) → ℂ) 0 (section43TimePositiveRegion n)}
  zero_mem' := by
    intro x hx
    simp
  add_mem' := by
    intro f g hf hg x hx
    simp [hf hx, hg hx]
  smul_mem' := by
    intro c f hf x hx
    simp [hf hx]

/-- The finite-time positive-energy quotient before the spatial Fourier layer. -/
abbrev Section43TimePositiveComponent (n : ℕ) :=
  (SchwartzMap (Fin n → ℝ) ℂ) ⧸ section43TimeVanishingSubmodule n

/-- The canonical quotient map onto the finite-time positive-energy component. -/
noncomputable def section43TimePositiveQuotientMap (n : ℕ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] Section43TimePositiveComponent n :=
  ContinuousLinearMap.mk
    (Submodule.mkQ (section43TimeVanishingSubmodule n))
    ((section43TimeVanishingSubmodule n).isOpenQuotientMap_mkQ.continuous)

/-- Equality on the closed positive orthant gives equality in the finite-time
quotient. -/
theorem section43TimePositiveQuotientMap_eq_of_eqOn_region
    {n : ℕ} {f g : SchwartzMap (Fin n → ℝ) ℂ}
    (hfg :
      Set.EqOn (f : (Fin n → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
        (section43TimePositiveRegion n)) :
    section43TimePositiveQuotientMap n f =
      section43TimePositiveQuotientMap n g := by
  change (Submodule.Quotient.mk f : Section43TimePositiveComponent n) =
    Submodule.Quotient.mk g
  rw [Submodule.Quotient.eq]
  change Set.EqOn ((f - g : SchwartzMap (Fin n → ℝ) ℂ) :
      (Fin n → ℝ) → ℂ) 0 (section43TimePositiveRegion n)
  intro x hx
  have hEq : f x = g x := hfg hx
  simp [hEq]

/-- Quotient equality is equality on the closed positive orthant. -/
theorem eqOn_region_of_section43TimePositiveQuotientMap_eq
    {n : ℕ} {f g : SchwartzMap (Fin n → ℝ) ℂ}
    (hfg :
      section43TimePositiveQuotientMap n f =
        section43TimePositiveQuotientMap n g) :
    Set.EqOn (f : (Fin n → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
      (section43TimePositiveRegion n) := by
  change (Submodule.Quotient.mk f : Section43TimePositiveComponent n) =
    Submodule.Quotient.mk g at hfg
  rw [Submodule.Quotient.eq] at hfg
  intro x hx
  have hx0 : ((f - g : SchwartzMap (Fin n → ℝ) ℂ) :
      (Fin n → ℝ) → ℂ) x = 0 := hfg hx
  exact sub_eq_zero.mp <| by simpa using hx0

/-- Pure tensor of one-variable time Schwartz functions. -/
noncomputable def section43TimeProductTensor
    {n : ℕ} (fs : Fin n → SchwartzMap ℝ ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.productTensor fs

/-- Identify finite time tuples with tuples of one-point time functions, so the
existing product-tensor density theorem at `d = 0` can be transported to
`SchwartzMap (Fin n → ℝ) ℂ`. -/
noncomputable def section43TimeAsOnePointCLE (n : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → Fin 1 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight
    (fun _ : Fin n => (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm)

@[simp] theorem section43TimeAsOnePointCLE_apply
    (n : ℕ) (x : Fin n → ℝ) (i : Fin n) (j : Fin 1) :
    section43TimeAsOnePointCLE n x i j = x i := by
  simp [section43TimeAsOnePointCLE, ContinuousLinearEquiv.piCongrRight]

@[simp] theorem section43TimeAsOnePointCLE_symm_apply
    (n : ℕ) (x : Fin n → Fin 1 → ℝ) (i : Fin n) :
    (section43TimeAsOnePointCLE n).symm x i = x i 0 := by
  change (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (x i) = x i 0
  simp [ContinuousLinearEquiv.coe_funUnique]

/-- Transporting a time product tensor to one-point time coordinates is the
product tensor of the transported one-variable factors. -/
theorem section43TimeAsOnePoint_productTensor
    {n : ℕ} (fs : Fin n → SchwartzMap ℝ ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43TimeAsOnePointCLE n).symm
        (section43TimeProductTensor fs)
      =
    SchwartzMap.productTensor
      (fun i : Fin n =>
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
          (fs i)) := by
  ext x
  simp [section43TimeProductTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.productTensor_apply]

/-- Pulling a one-point-coordinate product tensor back to ordinary time
coordinates is the product tensor of the pulled-back one-variable factors. -/
theorem section43TimeAsOnePoint_symm_productTensor
    {n : ℕ} (fs : Fin n → SchwartzMap (Fin 1 → ℝ) ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43TimeAsOnePointCLE n)
        (SchwartzMap.productTensor fs)
      =
    section43TimeProductTensor
      (fun i : Fin n =>
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
          (fs i)) := by
  ext x
  simp only [section43TimeProductTensor, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SchwartzMap.productTensor_apply, Function.comp_apply]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  congr 1

@[simp] theorem section43TimeAsOnePoint_comp_symm
    {n : ℕ} (f : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43TimeAsOnePointCLE n)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43TimeAsOnePointCLE n).symm f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp] theorem section43TimeAsOnePoint_symm_comp
    {n : ℕ} (f : SchwartzMap (Fin n → Fin 1 → ℝ) ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43TimeAsOnePointCLE n).symm
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43TimeAsOnePointCLE n) f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The span of ordinary finite-time product tensors is dense in the finite-time
Schwartz space.  This is `productTensor_span_dense 0 n` transported from
one-point spacetime coordinates to ordinary real time coordinates. -/
theorem section43_timeProductTensor_span_dense (n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            F = section43TimeProductTensor fs}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)) :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let B := SchwartzMap (Fin n → Fin 1 → ℝ) ℂ
  let P : Set A :=
    {F : A | ∃ fs : Fin n → SchwartzMap ℝ ℂ,
      F = section43TimeProductTensor fs}
  let M : Submodule ℂ A := Submodule.span ℂ P
  let P0 : Set B :=
    {F : B | ∃ fs : Fin n → SchwartzMap (Fin 1 → ℝ) ℂ,
      F = SchwartzMap.productTensor fs}
  let M0 : Submodule ℂ B := Submodule.span ℂ P0
  let toA : B →L[ℂ] A :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43TimeAsOnePointCLE n)
  let toB : A →L[ℂ] B :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (section43TimeAsOnePointCLE n).symm
  change Dense (M : Set A)
  have hM0_dense : Dense (M0 : Set B) := by
    simpa [M0, P0, B, SchwartzNPointSpace, NPointSpacetime] using
      productTensor_span_dense 0 n
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  let preM : Submodule ℂ B := M.topologicalClosure.comap toA.toLinearMap
  have hM0_le : M0 ≤ preM := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    rcases hy with ⟨fs, rfl⟩
    change toA (SchwartzMap.productTensor fs) ∈ M.topologicalClosure
    have hP : toA (SchwartzMap.productTensor fs) ∈ P := by
      refine ⟨fun i : Fin n =>
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm (fs i), ?_⟩
      exact section43TimeAsOnePoint_symm_productTensor fs
    exact M.le_topologicalClosure (Submodule.subset_span hP)
  have hpre_closed : IsClosed (preM : Set B) := by
    change IsClosed {y : B | toA y ∈ (M.topologicalClosure : Set A)}
    exact M.isClosed_topologicalClosure.preimage toA.continuous
  have htop_le_pre : (⊤ : Submodule ℂ B) ≤ preM := by
    have hclosure : M0.topologicalClosure ≤ preM :=
      M0.topologicalClosure_minimal hM0_le hpre_closed
    rwa [(Submodule.dense_iff_topologicalClosure_eq_top).mp hM0_dense] at hclosure
  have hxpre : toB x ∈ preM := htop_le_pre trivial
  change toA (toB x) ∈ M.topologicalClosure at hxpre
  simpa [toA, toB] using hxpre

/-- If a one-variable set of Schwartz functions is dense, then finite sums of
time product tensors with all factors in that set are dense in finite-time
Schwartz space. -/
theorem section43_timeProductTensor_span_dense_of_factor_dense
    {S : Set (SchwartzMap ℝ ℂ)}
    (hS : Dense S) (n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            (∀ i : Fin n, fs i ∈ S) ∧
            F = section43TimeProductTensor fs}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)) :
        Set (SchwartzMap (Fin n → ℝ) ℂ)) := by
  let E := SchwartzMap ℝ ℂ
  let A := SchwartzMap (Fin n → ℝ) ℂ
  let PS : Set A :=
    {F : A | ∃ fs : Fin n → E,
      (∀ i : Fin n, fs i ∈ S) ∧ F = section43TimeProductTensor fs}
  let MS : Submodule ℂ A := Submodule.span ℂ PS
  let Pall : Set A :=
    {F : A | ∃ fs : Fin n → E, F = section43TimeProductTensor fs}
  let Mall : Submodule ℂ A := Submodule.span ℂ Pall
  change Dense (MS : Set A)
  let D : Set (Fin n → E) := {fs | ∀ i : Fin n, fs i ∈ S}
  have hD : Dense D := by
    have hD' : Dense (Set.pi (Set.univ : Set (Fin n)) (fun _ : Fin n => S)) :=
      dense_pi (I := (Set.univ : Set (Fin n)))
        (s := fun _ : Fin n => S) (fun i _hi => hS)
    simpa [D, Set.pi] using hD'
  have hTcont :
      Continuous (fun fs : Fin n → E => section43TimeProductTensor fs) := by
    simpa [section43TimeProductTensor, E] using
      (SchwartzMap.productTensor_continuous (E := ℝ) (n := n))
  have hPall_le_MSclosure : Mall ≤ MS.topologicalClosure := by
    refine Submodule.span_le.mpr ?_
    intro F hF
    rcases hF with ⟨fs, rfl⟩
    have himage_subset :
        (fun gs : Fin n → E => section43TimeProductTensor gs) '' D ⊆
          (MS : Set A) := by
      rintro _ ⟨gs, hgs, rfl⟩
      exact Submodule.subset_span ⟨gs, hgs, rfl⟩
    have hmem_image_closure :
        section43TimeProductTensor fs ∈
          closure ((fun gs : Fin n → E => section43TimeProductTensor gs) '' D) := by
      exact hTcont.range_subset_closure_image_dense hD ⟨fs, rfl⟩
    change section43TimeProductTensor fs ∈ closure (MS : Set A)
    exact closure_mono himage_subset hmem_image_closure
  have hMall_dense : Dense (Mall : Set A) := by
    simpa [Mall, Pall, A, E] using section43_timeProductTensor_span_dense n
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hxMall : x ∈ Mall.topologicalClosure := by
    rw [(Submodule.dense_iff_topologicalClosure_eq_top).mp hMall_dense]
    trivial
  have hclosure_le : Mall.topologicalClosure ≤ MS.topologicalClosure :=
    Mall.topologicalClosure_minimal hPall_le_MSclosure MS.isClosed_topologicalClosure
  exact hclosure_le hxMall

/-- A compact subset of the strict positive half-line has a positive lower
margin from the boundary. -/
theorem exists_positive_margin_of_isCompact_subset_Ioi
    {K : Set ℝ} (hK_compact : IsCompact K) (hK_pos : K ⊆ Set.Ioi (0 : ℝ)) :
    ∃ δ > 0, K ⊆ Set.Ici δ := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hx0_min⟩ :=
      hK_compact.exists_isMinOn hne continuous_id.continuousOn
    have hx0_pos : 0 < x0 := hK_pos hx0
    refine ⟨x0 / 2, by linarith, ?_⟩
    intro x hx
    have hle : x0 ≤ x := isMinOn_iff.mp hx0_min x hx
    exact Set.mem_Ici.mpr (by linarith)
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

/-- A compact Schwartz source supported in the strict positive time orthant. -/
structure Section43CompactStrictPositiveTimeSource (n : ℕ) where
  f : SchwartzMap (Fin n → ℝ) ℂ
  positive :
    tsupport (f : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n
  compact : HasCompactSupport (f : (Fin n → ℝ) → ℂ)

namespace Section43CompactStrictPositiveTimeSource

private theorem ext_f {n : ℕ}
    {g h : Section43CompactStrictPositiveTimeSource n}
    (hf : g.f = h.f) : g = h := by
  cases g
  cases h
  simp at hf
  subst hf
  rfl

private theorem f_injective (n : ℕ) :
    Function.Injective
      (fun g : Section43CompactStrictPositiveTimeSource n => g.f) := by
  intro g h hf
  exact ext_f hf

instance (n : ℕ) : Zero (Section43CompactStrictPositiveTimeSource n) where
  zero :=
    { f := 0
      positive := by
        intro t ht
        simp at ht
      compact := by
        simpa using
          (HasCompactSupport.zero :
            HasCompactSupport (0 : (Fin n → ℝ) → ℂ)) }

instance (n : ℕ) : Add (Section43CompactStrictPositiveTimeSource n) where
  add g h :=
    { f := g.f + h.f
      positive := by
        intro t ht
        have ht' := tsupport_add (g.f : (Fin n → ℝ) → ℂ)
          (h.f : (Fin n → ℝ) → ℂ) ht
        exact ht'.elim (fun hg => g.positive hg) (fun hh => h.positive hh)
      compact := by
        simpa using HasCompactSupport.add g.compact h.compact }

instance (n : ℕ) : SMul ℕ (Section43CompactStrictPositiveTimeSource n) where
  smul m g :=
    { f := (m : ℂ) • g.f
      positive := by
        exact
          (tsupport_smul_subset_right
            (fun _ : Fin n → ℝ => (m : ℂ))
            (g.f : (Fin n → ℝ) → ℂ)).trans g.positive
      compact := by
        simpa using
          (HasCompactSupport.smul_left
            (f := fun _ : Fin n → ℝ => (m : ℂ))
            (f' := (g.f : (Fin n → ℝ) → ℂ)) g.compact) }

instance (n : ℕ) : AddCommMonoid (Section43CompactStrictPositiveTimeSource n) :=
  Function.Injective.addCommMonoid
    (fun g : Section43CompactStrictPositiveTimeSource n => g.f)
    (f_injective n) rfl
    (by intro g h; rfl)
    (by
      intro g m
      change (m : ℂ) • g.f = m • g.f
      rw [Nat.cast_smul_eq_nsmul ℂ])

instance (n : ℕ) : SMul ℂ (Section43CompactStrictPositiveTimeSource n) where
  smul c g :=
    { f := c • g.f
      positive := by
        exact
          (tsupport_smul_subset_right
            (fun _ : Fin n → ℝ => c)
            (g.f : (Fin n → ℝ) → ℂ)).trans g.positive
      compact := by
        simpa using
          (HasCompactSupport.smul_left
            (f := fun _ : Fin n → ℝ => c)
            (f' := (g.f : (Fin n → ℝ) → ℂ)) g.compact) }

private def fAddMonoidHom (n : ℕ) :
    Section43CompactStrictPositiveTimeSource n →+
      SchwartzMap (Fin n → ℝ) ℂ where
  toFun := fun g => g.f
  map_zero' := rfl
  map_add' := by intro g h; rfl

instance (n : ℕ) : Module ℂ (Section43CompactStrictPositiveTimeSource n) :=
  Function.Injective.module ℂ (fAddMonoidHom n)
    (by
      intro g h hf
      exact (f_injective n) hf)
    (by intro c g; rfl)

end Section43CompactStrictPositiveTimeSource

/-- Compact strict-positive finite-time support has a uniform positive margin
from every time wall. -/
theorem exists_positive_margin_of_compact_time_tsupport_subset_strictPositive
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ δ, 0 < δ ∧
      tsupport (g.f : (Fin n → ℝ) → ℂ) ⊆
        {τ | ∀ i : Fin n, δ ≤ τ i} := by
  classical
  let K : Set (Fin n → ℝ) := tsupport (g.f : (Fin n → ℝ) → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using g.compact
  by_cases hnonempty : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hnonempty
    have hcoord_margin :
        ∀ i : Fin n,
          ∃ δ > 0, ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ici δ := by
      intro i
      have himage_compact :
          IsCompact ((fun τ : Fin n → ℝ => τ i) '' K) :=
        hK_compact.image (continuous_apply i)
      have himage_pos :
          ((fun τ : Fin n → ℝ => τ i) '' K) ⊆ Set.Ioi (0 : ℝ) := by
        rintro _ ⟨τ, hτ, rfl⟩
        exact g.positive hτ i
      exact exists_positive_margin_of_isCompact_subset_Ioi himage_compact himage_pos
    choose δ hδ_pos hδ_supp using hcoord_margin
    let δmin : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
    have hδmin_pos : 0 < δmin := by
      obtain ⟨i, _hi, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty δ
      dsimp [δmin]
      rw [hmin]
      exact hδ_pos i
    refine ⟨δmin, hδmin_pos, ?_⟩
    intro τ hτ i
    have hδmin_le : δmin ≤ δ i := by
      dsimp [δmin]
      exact Finset.inf'_le δ (Finset.mem_univ i)
    have hcoord : τ i ∈ ((fun τ : Fin n → ℝ => τ i) '' K) :=
      ⟨τ, hτ, rfl⟩
    exact hδmin_le.trans (hδ_supp i hcoord)
  · refine ⟨1, by norm_num, ?_⟩
    intro τ _hτ i
    exact False.elim (hnonempty ⟨i⟩)

/-- Compact finite-time support is contained in some closed ball centered at
zero. -/
theorem exists_time_closedBall_of_compact_tsupport
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ R, 0 ≤ R ∧
      tsupport (g.f : (Fin n → ℝ) → ℂ) ⊆
        Metric.closedBall (0 : Fin n → ℝ) R := by
  let K : Set (Fin n → ℝ) := tsupport (g.f : (Fin n → ℝ) → ℂ)
  have hK_compact : IsCompact K := by
    simpa [K, HasCompactSupport] using g.compact
  obtain ⟨B, hB⟩ :=
    hK_compact.exists_bound_of_continuousOn
      (f := fun τ : Fin n → ℝ => ‖τ‖) continuous_norm.continuousOn
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro τ hτ
  have hτB : ‖τ‖ ≤ B := by
    have h := hB τ hτ
    simpa [Real.norm_eq_abs, norm_nonneg] using h
  have hτR : ‖τ‖ ≤ max B 0 := hτB.trans (le_max_left B 0)
  simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hτR

/-- In finite-dimensional time domain, continuity of a family of continuous
multilinear maps is equivalent to continuity of all applied scalar families. -/
theorem continuous_cmlm_apply_time
    (n r : ℕ)
    {X : Type*} [TopologicalSpace X]
    {L : X →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ} :
    Continuous L ↔
      ∀ m : Fin r → (Fin n → ℝ), Continuous fun x => L x m := by
  induction r generalizing X with
  | zero =>
      constructor
      · intro hL m
        exact
          (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin 0 => Fin n → ℝ) ℂ m).continuous.comp hL
      · intro h
        let e :=
          continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ
        have he : Continuous fun x => e (L x) := by
          simpa [e] using h (0 : Fin 0 → (Fin n → ℝ))
        have hback : Continuous fun x => e.symm (e (L x)) :=
          e.symm.continuous.comp he
        simpa [e] using hback
  | succ r ih =>
      constructor
      · intro hL m
        exact
          (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ m).continuous.comp hL
      · intro h
        let e :=
          continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ
        have hcurry : Continuous fun x => e (L x) := by
          refine (continuous_clm_apply
            (𝕜 := ℝ) (E := Fin n → ℝ)).2 ?_
          intro head
          refine (ih (L := fun x => e (L x) head)).2 ?_
          intro tail
          simpa [e, ContinuousMultilinearMap.curryLeft_apply] using
            h (Fin.cons head tail)
        have hback : Continuous fun x => e.symm (e (L x)) :=
          e.symm.continuous.comp hcurry
        simpa [e] using hback

/-- The topological support of a product tensor is contained in the product of
the topological supports of its one-variable compact factors. -/
theorem tsupport_section43TimeProductTensor_subset_pi_tsupport
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    tsupport
      ((section43TimeProductTensor (fun i : Fin n => (gs i).f) :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ)
      ⊆ {x | ∀ i : Fin n, x i ∈ tsupport ((gs i).f : ℝ → ℂ)} := by
  intro x hx i
  by_contra hxi
  have hlocal :
      ((gs i).f : ℝ → ℂ) =ᶠ[𝓝 (x i)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxi
  have hcoord :
      Tendsto (fun y : Fin n → ℝ => y i) (𝓝 x) (𝓝 (x i)) :=
    (continuous_apply i).continuousAt
  have hlocal_pi :
      ∀ᶠ y in 𝓝 x, (gs i).f (y i) = 0 :=
    hcoord.eventually hlocal
  have hprod_zero :
      ((section43TimeProductTensor (fun i : Fin n => (gs i).f) :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hlocal_pi] with y hy
    rw [section43TimeProductTensor, SchwartzMap.productTensor_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hy
  exact (notMem_tsupport_iff_eventuallyEq.mpr hprod_zero) hx

/-- A product tensor of compact one-variable strict-positive time sources has
compact support in finite time space. -/
theorem hasCompactSupport_section43TimeProductTensor
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    HasCompactSupport
      ((section43TimeProductTensor (fun i : Fin n => (gs i).f) :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) := by
  let K : Set (Fin n → ℝ) :=
    Set.pi Set.univ (fun i : Fin n => tsupport ((gs i).f : ℝ → ℂ))
  have hKcompact : IsCompact K := by
    exact isCompact_univ_pi (fun i => (gs i).compact.isCompact)
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro x hx
  have hx_tsupport :
      x ∈ tsupport
        ((section43TimeProductTensor (fun i : Fin n => (gs i).f) :
            SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) :=
    subset_tsupport _ hx
  have hxKset :
      x ∈ {x | ∀ i : Fin n, x i ∈ tsupport ((gs i).f : ℝ → ℂ)} :=
    tsupport_section43TimeProductTensor_subset_pi_tsupport gs hx_tsupport
  simpa [K, Set.pi] using hxKset

/-- The product of one-variable compact strict-positive time sources is a
compact strict-positive source in the finite time variables. -/
noncomputable def section43TimeProductSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    Section43CompactStrictPositiveTimeSource n :=
  { f := section43TimeProductTensor (fun i : Fin n => (gs i).f)
    positive := by
      intro x hx i
      exact (gs i).positive
        (tsupport_section43TimeProductTensor_subset_pi_tsupport gs hx i)
    compact := hasCompactSupport_section43TimeProductTensor gs }

/-- The raw multitime one-sided Laplace scalar of a compact strict-positive
finite-time source. -/
noncomputable def section43IteratedLaplaceRaw
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) : ℂ :=
  ∫ τ : Fin n → ℝ,
    Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
      g.f τ

/-- The cutoff version of the raw multitime Laplace scalar. -/
noncomputable def section43IteratedLaplaceCutoffFun
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) : ℂ :=
  section43TimePositiveCutoff n σ * section43IteratedLaplaceRaw n g σ

/-- On the closed positive orthant the cutoff multitime Laplace scalar agrees
with the raw scalar. -/
theorem section43IteratedLaplaceCutoffFun_eq_raw_of_mem
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n)
    {σ : Fin n → ℝ} (hσ : σ ∈ section43TimePositiveRegion n) :
    section43IteratedLaplaceCutoffFun n g σ =
      section43IteratedLaplaceRaw n g σ := by
  rw [section43IteratedLaplaceCutoffFun,
    section43TimePositiveCutoff_eq_one_of_mem hσ]
  simp

/-- For fixed source time `τ`, the finite-time Laplace integrand is smooth in
the positive-energy variable `σ`. -/
theorem contDiff_section43IteratedLaplaceRaw_integrand_sigma
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n)
    (τ : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun σ : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          g.f τ) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun σ : Fin n → ℝ => -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) := by
    apply ContDiff.neg
    apply ContDiff.sum
    intro i _hi
    have hcoord :
        ContDiff ℝ (⊤ : ℕ∞) (fun σ : Fin n → ℝ => (σ i : ℂ)) := by
      have hreal :
          ContDiff ℝ (⊤ : ℕ∞) (fun σ : Fin n → ℝ => σ i) := by
        simpa using
          ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
            (φ := fun _ => ℝ) i).contDiff :
            ContDiff ℝ (⊤ : ℕ∞) (fun σ : Fin n → ℝ =>
              (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
                (φ := fun _ => ℝ) i) σ))
      exact Complex.ofRealCLM.contDiff.comp hreal
    exact contDiff_const.mul hcoord
  exact (Complex.contDiff_exp.comp harg).mul contDiff_const

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise all-order derivative of the finite-time Laplace integrand has
derivative given by curry-left of the next pointwise derivative. -/
theorem hasFDerivAt_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft
    {n r : ℕ} (g : Section43CompactStrictPositiveTimeSource n)
    (σ τ : Fin n → ℝ) :
    HasFDerivAt
      (fun σ' : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun σ'' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
              g.f τ)
          σ')
      ((iteratedFDeriv ℝ (r + 1)
        (fun σ'' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
            g.f τ)
        σ).curryLeft)
      σ := by
  let G : (Fin n → ℝ) → ℂ := fun σ' =>
    Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
      g.f τ
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    simpa [G] using contDiff_section43IteratedLaplaceRaw_integrand_sigma g τ
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ r G) σ := by
    exact hGsmooth.contDiffAt.differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.2 (ENat.coe_lt_top r))
  have hderiv_eq :
      fderiv ℝ (iteratedFDeriv ℝ r G) σ =
        (iteratedFDeriv ℝ (r + 1) G σ).curryLeft := by
    ext v mtail
    rfl
  simpa [G, hderiv_eq] using hdiff.hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
/-- Integrated candidate for the `r`-th Fréchet derivative of the raw
multitime Laplace scalar.  The next estimates prove this integral is
integrable and equals the actual iterated derivative. -/
noncomputable def section43IteratedLaplaceRaw_iteratedFDerivCandidate
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
  ∫ τ : Fin n → ℝ,
    (iteratedFDeriv ℝ r
        (fun σ' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
            g.f τ)
        σ :
      ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ)

/-- A finite-time ambient Schwartz representative of the multitime
one-sided Laplace transform, modulo equality on the closed positive orthant. -/
def section43IteratedLaplaceRepresentative
    (n : ℕ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (Φ : SchwartzMap (Fin n → ℝ) ℂ) : Prop :=
  ∀ σ : Fin n → ℝ, σ ∈ section43TimePositiveRegion n →
    Φ σ = section43IteratedLaplaceRaw n g σ

/-- The multitime Laplace integrand of a product source factors coordinatewise.
This is the finite-product Fubini calculation needed for the product-source
representative theorem. -/
theorem section43TimeProductSource_integral_eq_product_raw
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (σ : Fin n → ℝ) :
    (∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (section43TimeProductSource gs).f τ) =
      ∏ i : Fin n,
        ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ i : ℂ)) * (gs i).f t := by
  have hpoint :
      (fun τ : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          (section43TimeProductSource gs).f τ)
        =
      (fun τ : Fin n → ℝ =>
        ∏ i : Fin n,
          Complex.exp (-(τ i : ℂ) * (σ i : ℂ)) * (gs i).f (τ i)) := by
    funext τ
    have hexp :
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) =
          ∏ i : Fin n, Complex.exp (-(τ i : ℂ) * (σ i : ℂ)) := by
      calc
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))
            = Complex.exp (∑ i : Fin n, -(τ i : ℂ) * (σ i : ℂ)) := by
                congr 1
                rw [← Finset.sum_neg_distrib]
                exact Finset.sum_congr rfl (fun i _hi => by ring)
        _ = ∏ i : Fin n, Complex.exp (-(τ i : ℂ) * (σ i : ℂ)) := by
                exact Complex.exp_sum Finset.univ
                  (fun i : Fin n => -(τ i : ℂ) * (σ i : ℂ))
    change
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          ((SchwartzMap.productTensor (fun i : Fin n => (gs i).f) :
              SchwartzMap (Fin n → ℝ) ℂ) τ) =
        ∏ i : Fin n, Complex.exp (-(τ i : ℂ) * (σ i : ℂ)) * (gs i).f (τ i)
    rw [SchwartzMap.productTensor_apply, hexp, Finset.prod_mul_distrib]
  rw [hpoint]
  exact integral_fintype_prod_volume_eq_prod
    (fun i : Fin n => fun t : ℝ =>
      Complex.exp (-(t : ℂ) * (σ i : ℂ)) * (gs i).f t)

/-- On the closed positive orthant, the product tensor of the one-variable
cutoff Laplace representatives is the multitime Laplace integral of the product
source. -/
theorem section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D)
    {σ : Fin n → ℝ} (hσ : σ ∈ section43TimePositiveRegion n) :
    (section43TimeProductTensor
      (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) :
        SchwartzMap (Fin n → ℝ) ℂ) σ =
    ∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (section43TimeProductSource gs).f τ := by
  rw [section43TimeProductSource_integral_eq_product_raw]
  rw [section43TimeProductTensor, SchwartzMap.productTensor_apply]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  rw [section43OneSidedLaplaceSchwartzRepresentative1D_apply,
    section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg (gs i) (hσ i)]
  rfl

/-- Product sources have the product tensor of the one-variable compact
Laplace representatives as their finite-time multitime representative. -/
theorem section43TimeProductTensor_oneSidedLaplaceRepresentative
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    section43IteratedLaplaceRepresentative n (section43TimeProductSource gs)
      (section43TimeProductTensor
        (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
  intro σ hσ
  simpa [section43IteratedLaplaceRaw] using
    section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral gs hσ

/-- Product-source representative existence, isolated from the harder
arbitrary-source representative theorem. -/
theorem exists_section43IteratedLaplaceRepresentative_productSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    ∃ Φ : SchwartzMap (Fin n → ℝ) ℂ,
      section43IteratedLaplaceRepresentative n (section43TimeProductSource gs) Φ :=
  ⟨section43TimeProductTensor
      (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)),
    section43TimeProductTensor_oneSidedLaplaceRepresentative gs⟩

end OSReconstruction
