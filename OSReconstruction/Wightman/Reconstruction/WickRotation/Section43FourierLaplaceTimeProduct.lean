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

attribute [local instance 101] secondCountableTopologyEither_of_left

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

/-- The real-linear functional whose exponential gives the finite-time
Laplace kernel for a fixed source-time vector `τ`. -/
noncomputable def section43TimeLaplaceLinearMap
    (n : ℕ) (τ : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℂ where
  toFun := fun σ => -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))
  map_add' := by
    intro σ σ'
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c σ
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    calc
      -(∑ i : Fin n, (τ i : ℂ) * ((c : ℂ) * (σ i : ℂ)))
          = -(∑ i : Fin n, (c : ℂ) * ((τ i : ℂ) * (σ i : ℂ))) := by
              congr 1
              exact Finset.sum_congr rfl (fun i _hi => by ring)
      _ = (RingHom.id ℝ) c • -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)) := by
              simp [Finset.mul_sum]

/-- Continuous version of the finite-time Laplace linear functional. -/
noncomputable def section43TimeLaplaceLinearCLM
    (n : ℕ) (τ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ContinuousLinearMap.mk (section43TimeLaplaceLinearMap n τ) (by
    have hcont :
        Continuous fun σ : Fin n → ℝ =>
          -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)) := by
      fun_prop
    simpa [section43TimeLaplaceLinearMap] using hcont)

@[simp] theorem section43TimeLaplaceLinearCLM_apply
    (n : ℕ) (τ σ : Fin n → ℝ) :
    section43TimeLaplaceLinearCLM n τ σ =
      -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)) := rfl

/-- A point in the unit closed ball around a finite-time vector has norm at
most `‖σ‖ + 1`. -/
theorem norm_time_le_norm_add_one_of_mem_closedBall
    (n : ℕ) (σ σ' : Fin n → ℝ)
    (hσ' : σ' ∈ Metric.closedBall σ (1 : ℝ)) :
    ‖σ'‖ ≤ ‖σ‖ + 1 := by
  have hdist : dist σ' σ ≤ (1 : ℝ) := by
    simpa [Metric.mem_closedBall] using hσ'
  have hsub : ‖σ' - σ‖ ≤ (1 : ℝ) := by
    simpa [dist_eq_norm] using hdist
  have htri : ‖σ'‖ ≤ ‖σ' - σ‖ + ‖σ‖ := by
    calc
      ‖σ'‖ = ‖(σ' - σ) + σ‖ := by
        simp
      _ ≤ ‖σ' - σ‖ + ‖σ‖ := norm_add_le _ _
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- On a compact time ball, the explicit Laplace linear functional has
operator norm bounded by the coordinate-sum radius. -/
theorem norm_section43TimeLaplaceLinearCLM_le
    (n : ℕ) (τ : Fin n → ℝ) {R : ℝ}
    (hR_nonneg : 0 ≤ R)
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R) :
    ‖section43TimeLaplaceLinearCLM n τ‖ ≤ ∑ _ : Fin n, R := by
  have hτ_norm : ‖τ‖ ≤ R :=
    norm_le_of_mem_time_closedBall_zero n τ hτ
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact Finset.sum_nonneg fun _ _ => hR_nonneg
  · intro σ
    have hsum :
        ‖∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)‖ ≤
          ∑ _ : Fin n, R * ‖σ‖ := by
      calc
        ‖∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)‖
            ≤ ∑ i : Fin n, ‖(τ i : ℂ) * (σ i : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _ : Fin n, R * ‖σ‖ := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              have hτi : |τ i| ≤ R := by
                have hcoord : ‖τ i‖ ≤ ‖τ‖ := norm_le_pi_norm τ i
                have hcoord_abs : |τ i| ≤ ‖τ‖ := by
                  simpa [Real.norm_eq_abs] using hcoord
                exact hcoord_abs.trans hτ_norm
              have hσi : |σ i| ≤ ‖σ‖ := by
                have hcoord : ‖σ i‖ ≤ ‖σ‖ := norm_le_pi_norm σ i
                simpa [Real.norm_eq_abs] using hcoord
              calc
                ‖(τ i : ℂ) * (σ i : ℂ)‖ = |τ i| * |σ i| := by
                  rw [norm_mul]
                  simp [Real.norm_eq_abs]
                _ ≤ R * ‖σ‖ := by
                  exact mul_le_mul hτi hσi (abs_nonneg _) hR_nonneg
    calc
      ‖section43TimeLaplaceLinearCLM n τ σ‖ =
          ‖∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)‖ := by
            rw [section43TimeLaplaceLinearCLM_apply, norm_neg]
      _ ≤ ∑ _ : Fin n, R * ‖σ‖ := hsum
      _ = (∑ _ : Fin n, R) * ‖σ‖ := by
            rw [Finset.sum_mul]

/-- On a compact product of a source-time ball and a unit σ-ball, the finite
time Laplace exponential is uniformly bounded. -/
theorem norm_exp_neg_timePair_le_local_time_closedBall
    (n : ℕ) (σ σ' τ : Fin n → ℝ)
    {R : ℝ} (hR_nonneg : 0 ≤ R)
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R)
    (hσ' : σ' ∈ Metric.closedBall σ (1 : ℝ)) :
    ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ ≤
      Real.exp (∑ _ : Fin n, R * (‖σ‖ + 1)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hτ_norm : ‖τ‖ ≤ R :=
    norm_le_of_mem_time_closedBall_zero n τ hτ
  have hσ_norm : ‖σ'‖ ≤ ‖σ‖ + 1 :=
    norm_time_le_norm_add_one_of_mem_closedBall n σ σ' hσ'
  have hterm :
      ∀ i : Fin n, |τ i * σ' i| ≤ R * (‖σ‖ + 1) := by
    intro i
    have hτi : |τ i| ≤ R := by
      have hcoord : ‖τ i‖ ≤ ‖τ‖ := norm_le_pi_norm τ i
      have hcoord_abs : |τ i| ≤ ‖τ‖ := by
        simpa [Real.norm_eq_abs] using hcoord
      exact hcoord_abs.trans hτ_norm
    have hσi : |σ' i| ≤ ‖σ‖ + 1 := by
      have hcoord : ‖σ' i‖ ≤ ‖σ'‖ := norm_le_pi_norm σ' i
      have hcoord_abs : |σ' i| ≤ ‖σ'‖ := by
        simpa [Real.norm_eq_abs] using hcoord
      exact hcoord_abs.trans hσ_norm
    calc
      |τ i * σ' i| = |τ i| * |σ' i| := by rw [abs_mul]
      _ ≤ R * (‖σ‖ + 1) := by
            exact mul_le_mul hτi hσi (abs_nonneg _) hR_nonneg
  have hsum_abs :
      -(∑ i : Fin n, τ i * σ' i) ≤
        ∑ i : Fin n, |τ i * σ' i| := by
    calc
      -(∑ i : Fin n, τ i * σ' i)
          ≤ |∑ i : Fin n, τ i * σ' i| := neg_le_abs _
      _ ≤ ∑ i : Fin n, |τ i * σ' i| := Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      ∑ i : Fin n, |τ i * σ' i| ≤
        ∑ _ : Fin n, R * (‖σ‖ + 1) := by
    exact Finset.sum_le_sum fun i _hi => hterm i
  have hre :
      (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))).re =
        -(∑ i : Fin n, τ i * σ' i) := by
    simp
  rw [hre]
  exact hsum_abs.trans hsum_bound

/-- A compact strict-positive finite-time source is uniformly bounded on every
closed time ball. -/
theorem exists_norm_bound_section43CompactStrictPositiveTimeSource_on_time_closedBall
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) (R : ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ τ ∈ Metric.closedBall (0 : Fin n → ℝ) R, ‖g.f τ‖ ≤ Cg := by
  let K : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  have hK_compact : IsCompact K := isCompact_closedBall (0 : Fin n → ℝ) R
  have hcont : Continuous fun τ : Fin n → ℝ => ‖g.f τ‖ :=
    continuous_norm.comp g.f.continuous
  obtain ⟨B, hB⟩ :=
    hK_compact.exists_bound_of_continuousOn
      (f := fun τ : Fin n → ℝ => ‖g.f τ‖) hcont.continuousOn
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro τ hτ
  have hτB : ‖g.f τ‖ ≤ B := by
    have h := hB τ hτ
    simpa [Real.norm_eq_abs, norm_nonneg] using h
  exact hτB.trans (le_max_left B 0)

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

set_option backward.isDefEq.respectTransparency false in
/-- For a smooth function of two variables, iterated derivatives of the partial
evaluation in the first variable are obtained by composing the full derivative
with the left injection. -/
theorem iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl_of_contDiff
    {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E₁ × E₂ → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E₂) (l : ℕ)
    (x : E₁) :
    iteratedFDeriv ℝ l (fun x' => f (x', y)) x =
      (iteratedFDeriv ℝ l f (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂) := by
  have htranslate : ∀ x',
      iteratedFDeriv ℝ l (fun z : E₁ × E₂ => f (z + (0, y))) (x', (0 : E₂)) =
        iteratedFDeriv ℝ l f (x' + 0, (0 : E₂) + y) := by
    intro x'
    rw [iteratedFDeriv_comp_add_right' l (0, y)]
    simp [Prod.add_def]
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E₁ × E₂ => f (z + ((0 : E₁), y))) :=
    hf.comp ((contDiff_id.add contDiff_const).of_le le_top)
  have hinl_comp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.inl ℝ E₁ E₂) hcomp x
      (by exact_mod_cast le_top (a := (l : ℕ∞)))
  have hlhs :
      (fun x' => f (x', y)) =
        (fun z : E₁ × E₂ => f (z + (0, y))) ∘
          (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    ext x'
    simp [ContinuousLinearMap.inl_apply]
  rw [hlhs, hinl_comp]
  exact congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F =>
      A.compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
    (by simpa [ContinuousLinearMap.inl_apply] using htranslate x)

/-- For fixed `σ`, the raw finite-time Laplace integrand is continuous in the
source time variable. -/
theorem continuous_section43IteratedLaplaceRaw_integrand_tau
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    Continuous fun τ : Fin n → ℝ =>
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        g.f τ := by
  have harg : Continuous fun τ : Fin n → ℝ =>
      -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)) := by
    fun_prop
  exact (Complex.continuous_exp.comp harg).mul g.f.continuous

/-- For fixed `σ`, the raw finite-time Laplace integrand is compactly supported
in the source time variable. -/
theorem hasCompactSupport_section43IteratedLaplaceRaw_integrand_of_compact
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    HasCompactSupport fun τ : Fin n → ℝ =>
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        g.f τ := by
  rcases exists_time_closedBall_of_compact_tsupport g with
    ⟨R, _hR_nonneg, hR_supp⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℝ) R) ?_
  intro τ hτ_support
  by_contra hτ_ball
  have hnot_tsupport :
      τ ∉ tsupport (g.f : (Fin n → ℝ) → ℂ) := by
    intro hτ_tsupport
    exact hτ_ball (hR_supp hτ_tsupport)
  have hnot_support : τ ∉ Function.support (g.f : (Fin n → ℝ) → ℂ) := by
    intro hsupport
    exact hnot_tsupport (subset_tsupport _ hsupport)
  have hzero : g.f τ = 0 := by
    by_contra hne
    exact hnot_support hne
  exact hτ_support (by simp [hzero])

/-- For fixed `σ`, the raw finite-time Laplace integrand is integrable in the
source time variable. -/
theorem integrable_section43IteratedLaplaceRaw_integrand_of_compact
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    Integrable fun τ : Fin n → ℝ =>
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        g.f τ :=
  (continuous_section43IteratedLaplaceRaw_integrand_tau n g σ).integrable_of_hasCompactSupport
    (hasCompactSupport_section43IteratedLaplaceRaw_integrand_of_compact n g σ)

set_option backward.isDefEq.respectTransparency false in
/-- For fixed `σ`, every pointwise σ-derivative of the raw finite-time
Laplace integrand is continuous in the source time variable. -/
theorem continuous_section43IteratedLaplaceRaw_integrand_iteratedFDeriv
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    Continuous fun τ : Fin n → ℝ =>
      iteratedFDeriv ℝ r
        (fun σ' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
            g.f τ)
        σ := by
  let F : (Fin n → ℝ) × (Fin n → ℝ) → ℂ := fun p =>
    Complex.exp (-(∑ i : Fin n, (p.2 i : ℂ) * (p.1 i : ℂ))) *
      g.f p.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          -(∑ i : Fin n, (p.2 i : ℂ) * (p.1 i : ℂ))) := by
      apply ContDiff.neg
      apply ContDiff.sum
      intro i _hi
      have hτcoord : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.2 i : ℂ)) := by
        have hreal : ContDiff ℝ (⊤ : ℕ∞)
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) := by
          simpa using
            (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
              (φ := fun _ => ℝ) i).contDiff :
                ContDiff ℝ (⊤ : ℕ∞) (fun τ : Fin n → ℝ =>
                  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
                    (φ := fun _ => ℝ) i) τ)).comp contDiff_snd)
        exact Complex.ofRealCLM.contDiff.comp hreal
      have hσcoord : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i : ℂ)) := by
        have hreal : ContDiff ℝ (⊤ : ℕ∞)
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) := by
          simpa using
            (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
              (φ := fun _ => ℝ) i).contDiff :
                ContDiff ℝ (⊤ : ℕ∞) (fun σ : Fin n → ℝ =>
                  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n)
                    (φ := fun _ => ℝ) i) σ)).comp contDiff_fst)
        exact Complex.ofRealCLM.contDiff.comp hreal
      exact hτcoord.mul hσcoord
    have hg : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g.f p.2) := by
      exact g.f.smooth'.comp contDiff_snd
    exact (Complex.contDiff_exp.comp harg).mul hg
  let A :
      ContinuousMultilinearMap ℝ
          (fun _ : Fin r => (Fin n → ℝ) × (Fin n → ℝ)) ℂ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))
  have hfull : Continuous fun τ : Fin n → ℝ =>
      iteratedFDeriv ℝ r F (σ, τ) := by
    have hderiv_cont : Continuous (iteratedFDeriv ℝ r F) := by
      exact hF.continuous_iteratedFDeriv
        (by exact_mod_cast le_top (a := (r : ℕ∞)))
    exact hderiv_cont.comp (continuous_const.prodMk continuous_id)
  have hA : Continuous fun τ : Fin n → ℝ =>
      A (iteratedFDeriv ℝ r F (σ, τ)) := A.continuous.comp hfull
  have heq :
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun σ' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
              g.f τ)
          σ)
        =
        fun τ : Fin n → ℝ => A (iteratedFDeriv ℝ r F (σ, τ)) := by
    funext τ
    simp [A, F,
      iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl_of_contDiff F hF τ r σ]
  rw [heq]
  exact hA

/-- If the source time variable lies outside the topological support of the
compact source, then every σ-derivative of the pointwise Laplace integrand is
zero. -/
theorem section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    {τ : Fin n → ℝ}
    (hτ : τ ∉ tsupport (g.f : (Fin n → ℝ) → ℂ)) :
    iteratedFDeriv ℝ r
      (fun σ : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          g.f τ) =
      0 := by
  have hnot_support : τ ∉ Function.support (g.f : (Fin n → ℝ) → ℂ) := by
    intro hsupport
    exact hτ (subset_tsupport _ hsupport)
  have hzero : g.f τ = 0 := by
    by_contra hne
    exact hnot_support hne
  have hfun :
      (fun σ : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          g.f τ) =
        fun _ => 0 := by
    funext σ
    simp [hzero]
  rw [hfun]
  funext σ
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Explicit norm bound for every σ-derivative of the pointwise finite-time
Laplace integrand. -/
theorem norm_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_le
    (n r : ℕ) (τ σ : Fin n → ℝ) (c : ℂ) :
    ‖iteratedFDeriv ℝ r
      (fun σ' : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) * c)
      σ‖ ≤
      r.factorial *
        ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ *
        ‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖c‖ := by
  let L : (Fin n → ℝ) →L[ℝ] ℂ := section43TimeLaplaceLinearCLM n τ
  let f : (Fin n → ℝ) → ℂ := fun x => Complex.exp (L x)
  have hf_cont : ContDiffAt ℝ (r : ℕ) f σ := by
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
      simpa [f] using (Complex.contDiff_exp.comp L.contDiff)
    exact hf.contDiffAt.of_le (by exact mod_cast le_top)
  have hfun :
      (fun σ' : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) * c)
        = fun σ' : Fin n → ℝ => f σ' • c := by
    funext σ'
    simp [f, L, section43TimeLaplaceLinearCLM_apply, smul_eq_mul]
  rw [hfun]
  rw [iteratedFDeriv_smul_const_apply (v := c) hf_cont]
  have hcomp :=
    ((ContinuousLinearMap.id ℝ ℂ).smulRight c).norm_compContinuousMultilinearMap_le
      (iteratedFDeriv ℝ r f σ)
  have hf_bound :
      ‖iteratedFDeriv ℝ r f σ‖ ≤
        r.factorial * ‖Complex.exp (L σ)‖ * ‖L‖ ^ r := by
    simpa [f] using norm_iteratedFDeriv_cexp_comp_clm_le L σ r
  have hsmul_norm_le :
      ‖((ContinuousLinearMap.id ℝ ℂ).smulRight c)‖ ≤ ‖c‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) ?_
    intro z
    simp [ContinuousLinearMap.smulRight_apply, mul_comm]
  calc
    ‖((ContinuousLinearMap.id ℝ ℂ).smulRight c).compContinuousMultilinearMap
        (iteratedFDeriv ℝ r f σ)‖
        ≤ ‖((ContinuousLinearMap.id ℝ ℂ).smulRight c)‖ *
            ‖iteratedFDeriv ℝ r f σ‖ := hcomp
    _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ r f σ‖ := by
          exact mul_le_mul_of_nonneg_right hsmul_norm_le (norm_nonneg _)
    _ ≤ ‖c‖ * (r.factorial * ‖Complex.exp (L σ)‖ * ‖L‖ ^ r) := by
          exact mul_le_mul_of_nonneg_left hf_bound (norm_nonneg c)
    _ =
        r.factorial *
          ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ *
          ‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖c‖ := by
          simp [L]
          ring

set_option backward.isDefEq.respectTransparency false in
/-- Compact local domination for the curry-left pointwise derivative of the
raw finite-time Laplace integrand. -/
theorem section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft_local_bound_of_compact
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    ∃ bound : (Fin n → ℝ) → ℝ,
      Integrable bound ∧
      ∀ᵐ τ, ∀ σ' ∈ Metric.closedBall σ (1 : ℝ),
        ‖(iteratedFDeriv ℝ (r + 1)
          (fun σ'' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
              g.f τ)
          σ').curryLeft‖ ≤ bound τ := by
  classical
  rcases exists_time_closedBall_of_compact_tsupport g with
    ⟨R, hR_nonneg, hR_supp⟩
  let Kτ : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  rcases exists_norm_bound_section43CompactStrictPositiveTimeSource_on_time_closedBall
    n g R with ⟨Cg, hCg_nonneg, hCg_bound⟩
  let Cexp : ℝ := Real.exp (∑ _ : Fin n, R * (‖σ‖ + 1))
  let CL : ℝ := ∑ _ : Fin n, R
  let C : ℝ := (r + 1).factorial * Cexp * CL ^ (r + 1) * Cg
  refine ⟨Set.indicator Kτ (fun _ => C), ?_, ?_⟩
  · simpa [Kτ, C] using integrable_indicator_time_closedBall_const n R C
  · filter_upwards with τ σ' hσ'
    by_cases hτ_mem : τ ∈ Kτ
    · rw [Set.indicator_of_mem hτ_mem]
      have hExp :
          ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ ≤
            Cexp := by
        simpa [Cexp, Kτ] using
          norm_exp_neg_timePair_le_local_time_closedBall
            n σ σ' τ hR_nonneg hτ_mem hσ'
      have hL :
          ‖section43TimeLaplaceLinearCLM n τ‖ ≤ CL := by
        simpa [CL, Kτ] using
          norm_section43TimeLaplaceLinearCLM_le
            n τ hR_nonneg hτ_mem
      have hLpow :
          ‖section43TimeLaplaceLinearCLM n τ‖ ^ (r + 1) ≤
            CL ^ (r + 1) := by
        exact pow_le_pow_left₀ (norm_nonneg _) hL (r + 1)
      have hSrc : ‖g.f τ‖ ≤ Cg := hCg_bound τ (by simpa [Kτ] using hτ_mem)
      have hmain :=
        norm_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_le
          n (r + 1) τ σ' (g.f τ)
      have hbase :
          ‖(iteratedFDeriv ℝ (r + 1)
            (fun σ'' : Fin n → ℝ =>
              Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
                g.f τ)
            σ').curryLeft‖ ≤
            (r + 1).factorial * Cexp * CL ^ (r + 1) * Cg := by
        calc
          ‖(iteratedFDeriv ℝ (r + 1)
            (fun σ'' : Fin n → ℝ =>
              Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
                g.f τ)
            σ').curryLeft‖ =
              ‖iteratedFDeriv ℝ (r + 1)
                (fun σ'' : Fin n → ℝ =>
                  Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
                    g.f τ)
                σ'‖ := by
                rw [ContinuousMultilinearMap.curryLeft_norm]
          _ ≤
              (r + 1).factorial *
                ‖Complex.exp
                  (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ *
                ‖section43TimeLaplaceLinearCLM n τ‖ ^ (r + 1) *
                ‖g.f τ‖ := hmain
          _ ≤ (r + 1).factorial * Cexp *
              CL ^ (r + 1) * Cg := by
                have hEL :
                    ‖Complex.exp
                      (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ *
                      ‖section43TimeLaplaceLinearCLM n τ‖ ^ (r + 1) ≤
                      Cexp * CL ^ (r + 1) := by
                  exact mul_le_mul hExp hLpow
                    (pow_nonneg (norm_nonneg _) _)
                    (Real.exp_pos _).le
                have hELS :
                    ‖Complex.exp
                      (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ *
                      ‖section43TimeLaplaceLinearCLM n τ‖ ^ (r + 1) *
                      ‖g.f τ‖ ≤
                      Cexp * CL ^ (r + 1) * Cg := by
                  exact mul_le_mul hEL hSrc (norm_nonneg _)
                    (mul_nonneg (Real.exp_pos _).le
                      (pow_nonneg (Finset.sum_nonneg fun _ _ => hR_nonneg) _))
                have hA_nonneg : 0 ≤ ((r + 1).factorial : ℝ) :=
                  Nat.cast_nonneg _
                simpa [mul_assoc] using
                  mul_le_mul_of_nonneg_left hELS hA_nonneg
      simpa [C, mul_assoc] using hbase
    · rw [Set.indicator_of_notMem hτ_mem]
      have hnot_tsupport :
          τ ∉ tsupport (g.f : (Fin n → ℝ) → ℂ) := by
        intro hτ_support
        exact hτ_mem (by simpa [Kτ] using hR_supp hτ_support)
      have hzero_fun :=
        section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport
          n (r + 1) g hnot_tsupport
      have hzero_at :
          iteratedFDeriv ℝ (r + 1)
            (fun σ'' : Fin n → ℝ =>
              Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
                g.f τ)
            σ' = 0 := by
        simpa using congrFun hzero_fun σ'
      simp [hzero_at]

set_option backward.isDefEq.respectTransparency false in
/-- Under compact source support, every pointwise σ-derivative of the raw
finite-time Laplace integrand is Bochner-integrable in the source time
variable. -/
theorem integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    Integrable
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun σ' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
              g.f τ)
          σ) := by
  have hmeas : AEStronglyMeasurable
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun σ' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
              g.f τ)
          σ) :=
    (continuous_section43IteratedLaplaceRaw_integrand_iteratedFDeriv
      n r g σ).aestronglyMeasurable
  cases r with
  | zero =>
      let e :=
        continuousMultilinearCurryFin0 ℝ (Fin n → ℝ) ℂ
      have hbase :
          Integrable
            (fun τ : Fin n → ℝ =>
              Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
                g.f τ) :=
        integrable_section43IteratedLaplaceRaw_integrand_of_compact n g σ
      have hcomp :
          Integrable
            (fun τ : Fin n → ℝ =>
              e.symm
                (Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
                  g.f τ)) :=
        (e.symm : ℂ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Fin n → ℝ) ℂ).integrable_comp hbase
      convert hcomp using 1
  | succ r =>
      rcases
        section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft_local_bound_of_compact
          n r g σ with
        ⟨bound, hbound_int, hbound⟩
      have hσ_self : σ ∈ Metric.closedBall σ (1 : ℝ) := by
        simp [Metric.mem_closedBall]
      refine Integrable.mono' hbound_int ?_ ?_
      · simpa using hmeas
      · exact hbound.mono fun τ hτ => by
          have hτσ := hτ σ hσ_self
          simpa [ContinuousMultilinearMap.curryLeft_norm] using hτσ

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

set_option backward.isDefEq.respectTransparency false in
/-- The integrated all-order derivative candidate has derivative given by the
curry-left of the next integrated candidate. -/
theorem section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    HasFDerivAt
      (fun σ' : Fin n → ℝ =>
        section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ')
      ((section43IteratedLaplaceRaw_iteratedFDerivCandidate n (r + 1) g σ).curryLeft)
      σ := by
  classical
  let Fint : (Fin n → ℝ) → (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
    fun σ' τ =>
      iteratedFDeriv ℝ r
        (fun σ'' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
            g.f τ)
        σ'
  let Fderiv : (Fin n → ℝ) → (Fin n → ℝ) →
      (Fin n → ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
    fun σ' τ =>
      (iteratedFDeriv ℝ (r + 1)
        (fun σ'' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
            g.f τ)
        σ').curryLeft
  rcases
    section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft_local_bound_of_compact
      n r g σ with
    ⟨bound, hbound_int, hbound⟩
  have hs : Metric.closedBall σ (1 : ℝ) ∈ 𝓝 σ :=
    Metric.closedBall_mem_nhds σ zero_lt_one
  have hF_meas : ∀ᶠ σ' in 𝓝 σ, AEStronglyMeasurable (Fint σ') := by
    exact Filter.Eventually.of_forall fun σ' =>
      (integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
        n r g σ').aestronglyMeasurable
  have hF_int : Integrable (Fint σ) := by
    simpa [Fint] using
      integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
        n r g σ
  have hbound' : ∀ᵐ τ : Fin n → ℝ, ∀ σ' ∈ Metric.closedBall σ (1 : ℝ),
      ‖Fderiv σ' τ‖ ≤ bound τ := by
    simpa [Fderiv] using hbound
  let Phi : (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ :=
    fun τ =>
      iteratedFDeriv ℝ (r + 1)
        (fun σ'' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
            g.f τ)
        σ
  have hnext_int :
      @Integrable
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        SeminormedAddGroup.toContinuousENorm
        (Fin n → ℝ) _ Phi volume := by
    simpa [Phi] using
      integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
        n (r + 1) g σ
  have hcurry_lipschitz :
      LipschitzWith 1
        (fun L : ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ =>
          L.curryLeft) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro L M
    simp only [NNReal.coe_one, one_mul]
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : L.curryLeft - M.curryLeft = (L - M).curryLeft := by
      ext v mtail
      simp [ContinuousMultilinearMap.curryLeft_apply]
    rw [hsub, ContinuousMultilinearMap.curryLeft_norm]
  have hFderiv_int :
      @Integrable
        ((Fin n → ℝ) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        SeminormedAddGroup.toContinuousENorm
        (Fin n → ℝ) _ (Fderiv σ) volume := by
    refine Integrable.mono
      (f := Fderiv σ)
      (g := Phi)
      hnext_int ?_ ?_
    · have hmeas :
          AEStronglyMeasurable
            (fun τ : Fin n → ℝ => (Phi τ).curryLeft) :=
          hcurry_lipschitz.continuous.comp_aestronglyMeasurable
            hnext_int.aestronglyMeasurable
      simpa [Fderiv, Phi] using hmeas
    · filter_upwards with τ
      simp [Fderiv, Phi, ContinuousMultilinearMap.curryLeft_norm]
  have hFderiv_meas := hFderiv_int.aestronglyMeasurable
  have hdiff : ∀ᵐ τ : Fin n → ℝ, ∀ σ' ∈ Metric.closedBall σ (1 : ℝ),
      HasFDerivAt (Fint · τ) (Fderiv σ' τ) σ' := by
    filter_upwards with τ σ' _hσ'
    simpa [Fint, Fderiv] using
      hasFDerivAt_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft
        (r := r) g σ' τ
  have hmain :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume)
      (F := Fint) (F' := Fderiv) (x₀ := σ)
      (s := Metric.closedBall σ (1 : ℝ)) (bound := bound)
      hs hF_meas hF_int hFderiv_meas hbound' hbound_int hdiff
  have hderivIntegral :
      (∫ τ : Fin n → ℝ, Fderiv σ τ) =
        ((∫ τ : Fin n → ℝ, Phi τ).curryLeft) := by
    letI : SeminormedAddCommGroup
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ) :=
      NormedAddCommGroup.toSeminormedAddCommGroup
    letI : SeminormedAddCommGroup
        ((Fin n → ℝ) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ) :=
      NormedAddCommGroup.toSeminormedAddCommGroup
    let curryLI :
        ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ →ₗᵢ[ℝ]
          ((Fin n → ℝ) →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ) :=
      { toLinearMap :=
          { toFun := fun L => L.curryLeft
            map_add' := by
              intro L M
              rfl
            map_smul' := by
              intro c L
              rfl }
        norm_map' := by
          intro L
          exact ContinuousMultilinearMap.curryLeft_norm L }
    haveI : CompleteSpace
        (ContinuousMultilinearMap ℝ
          (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ) := inferInstance
    change (∫ τ : Fin n → ℝ, curryLI (Phi τ)) =
      curryLI (∫ τ : Fin n → ℝ, Phi τ)
    exact
      (ContinuousLinearMap.integral_comp_comm
          (𝕜 := ℝ)
          (E := ContinuousMultilinearMap ℝ
            (fun _ : Fin (r + 1) => Fin n → ℝ) ℂ)
          (Fₗ := (Fin n → ℝ) →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ)
          (X := Fin n → ℝ)
          (μ := volume)
          curryLI.toContinuousLinearMap hnext_int)
  rw [hderivIntegral] at hmain
  simpa [section43IteratedLaplaceRaw_iteratedFDerivCandidate,
    Fint, Fderiv] using hmain

set_option backward.isDefEq.respectTransparency false in
/-- The iterated derivatives of the raw finite-time Laplace scalar are the
integrated pointwise derivative candidates. -/
theorem section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ =
      section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ := by
  classical
  let G : (Fin n → ℝ) → ℂ := fun σ' =>
    section43IteratedLaplaceRaw n g σ'
  induction r generalizing σ with
  | zero =>
      ext m
      have hint :
          Integrable
            (fun τ : Fin n → ℝ =>
              iteratedFDeriv ℝ 0
                (fun σ' : Fin n → ℝ =>
                  Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
                    g.f τ)
                σ) := by
        simpa using
          integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
            n 0 g σ
      change
        section43IteratedLaplaceRaw n g σ =
          (∫ τ : Fin n → ℝ,
            iteratedFDeriv ℝ 0
              (fun σ' : Fin n → ℝ =>
                Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
                  g.f τ)
              σ) m
      rw [ContinuousMultilinearMap.integral_apply hint m]
      simp [section43IteratedLaplaceRaw, iteratedFDeriv_zero_apply]
  | succ r ih =>
      have hfun :
          iteratedFDeriv ℝ r G =
          fun σ' : Fin n → ℝ =>
            section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ' := by
        funext σ'
        simpa [G] using ih σ'
      have hfd :
          fderiv ℝ (iteratedFDeriv ℝ r G) σ =
            (section43IteratedLaplaceRaw_iteratedFDerivCandidate
              n (r + 1) g σ).curryLeft := by
        have hderiv :=
          section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
            n r g σ
        rw [hfun]
        exact hderiv.fderiv
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfd]
      exact ContinuousMultilinearMap.uncurry_curryLeft _

set_option backward.isDefEq.respectTransparency false in
/-- The raw finite-time Laplace scalar is ambient smooth in the finite-time
positive-energy variable. -/
theorem section43IteratedLaplaceRaw_contDiff
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43IteratedLaplaceRaw n g) := by
  classical
  let G : (Fin n → ℝ) → ℂ := fun σ =>
    section43IteratedLaplaceRaw n g σ
  change ContDiff ℝ (↑(⊤ : ℕ∞)) G
  refine contDiff_of_differentiable_iteratedFDeriv
    (𝕜 := ℝ) (E := Fin n → ℝ) (F := ℂ) (f := G) (n := (⊤ : ℕ∞)) ?_
  intro r _hr
  have hfun :
      iteratedFDeriv ℝ r G =
      fun σ : Fin n → ℝ =>
        section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ := by
    funext σ
    simpa [G] using
      section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate n r g σ
  rw [hfun]
  intro σ
  exact
    (section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
      n r g σ).differentiableAt

set_option backward.isDefEq.respectTransparency false in
/-- Rapid decay of the actual all-order derivatives of the raw finite-time
Laplace scalar on the unit one-sided time collar. -/
theorem section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
    (n r s : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ section43TimePositiveThickening n 1,
        (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ‖ ≤ C := by
  classical
  rcases exists_positive_margin_of_compact_time_tsupport_subset_strictPositive g with
    ⟨δ, hδ_pos, hδ_supp⟩
  rcases exists_time_closedBall_of_compact_tsupport g with
    ⟨R, hR_nonneg, hR_supp⟩
  rcases exists_norm_bound_section43CompactStrictPositiveTimeSource_on_time_closedBall
    n g R with ⟨Cg, hCg_nonneg, hCg_bound⟩
  let Kτ : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) R
  let CL : ℝ := ∑ _ : Fin n, R
  let Cderiv : ℝ := r.factorial * CL ^ r * Cg
  let M : ℝ := ∫ τ : Fin n → ℝ, Set.indicator Kτ (fun _ : Fin n → ℝ => Cderiv) τ
  rcases exp_margin_sum_controls_thickened_time_polynomial
      (n := n) (δ := δ) (ε := (1 : ℝ)) (R := R)
      hδ_pos zero_le_one hR_nonneg s with
    ⟨Ct, hCt_nonneg, hCt_bound⟩
  let C : ℝ := Ct * M
  have hCL_nonneg : 0 ≤ CL := by
    exact Finset.sum_nonneg fun _ _ => hR_nonneg
  have hCderiv_nonneg : 0 ≤ Cderiv := by
    dsimp [Cderiv]
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun τ => by
      by_cases hτ : τ ∈ Kτ
      · simp [Set.indicator_of_mem hτ, hCderiv_nonneg]
      · simp [Set.indicator_of_notMem hτ]
  refine ⟨C, mul_nonneg hCt_nonneg hM_nonneg, ?_⟩
  intro σ hσ
  let Eσ : ℝ :=
    Real.exp (∑ _ : Fin n, R * (1 : ℝ)) *
      Real.exp (-(δ * ∑ i : Fin n, (σ i + 1)))
  let G : (Fin n → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
    fun τ =>
      iteratedFDeriv ℝ r
        (fun σ' : Fin n → ℝ =>
          Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
            g.f τ)
        σ
  have hE_nonneg : 0 ≤ Eσ := by
    dsimp [Eσ]
    positivity
  have hbound_int :
      Integrable
        (fun τ : Fin n → ℝ =>
          Eσ * Set.indicator Kτ (fun _ : Fin n → ℝ => Cderiv) τ) :=
    (integrable_indicator_time_closedBall_const n R Cderiv).const_mul Eσ
  have hpoint : ∀ τ : Fin n → ℝ,
      ‖G τ‖ ≤ Eσ * Set.indicator Kτ (fun _ : Fin n → ℝ => Cderiv) τ := by
    intro τ
    by_cases hτK : τ ∈ Kτ
    · rw [Set.indicator_of_mem hτK]
      by_cases hτ_supp : τ ∈ tsupport (g.f : (Fin n → ℝ) → ℂ)
      · have hτ_low : ∀ i : Fin n, δ ≤ τ i := hδ_supp hτ_supp
        have hτ_norm : ‖τ‖ ≤ R := by
          simpa [Kτ] using norm_le_of_mem_time_closedBall_zero n τ hτK
        have hExp :
            ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ ≤ Eσ := by
          simpa [Eσ] using
            norm_exp_neg_timePair_le_exp_thickened_margin_sum
              n hδ_pos zero_le_one hR_nonneg σ τ hσ hτ_low hτ_norm
        have hL :
            ‖section43TimeLaplaceLinearCLM n τ‖ ≤ CL := by
          simpa [CL, Kτ] using
            norm_section43TimeLaplaceLinearCLM_le n τ hR_nonneg hτK
        have hLpow :
            ‖section43TimeLaplaceLinearCLM n τ‖ ^ r ≤ CL ^ r := by
          exact pow_le_pow_left₀ (norm_nonneg _) hL r
        have hSrc : ‖g.f τ‖ ≤ Cg := hCg_bound τ (by simpa [Kτ] using hτK)
        have hmain :=
          norm_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_le
            n r τ σ (g.f τ)
        have hLCg :
            ‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖g.f τ‖ ≤
              CL ^ r * Cg := by
          exact mul_le_mul hLpow hSrc (norm_nonneg _)
            (pow_nonneg hCL_nonneg _)
        have hExpLCg :
            ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ *
                (‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖g.f τ‖) ≤
              Eσ * (CL ^ r * Cg) := by
          exact mul_le_mul hExp hLCg
            (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
            hE_nonneg
        calc
          ‖G τ‖ ≤
              r.factorial *
                ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ *
                ‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖g.f τ‖ := by
                simpa [G] using hmain
          _ = r.factorial *
                (‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ)))‖ *
                  (‖section43TimeLaplaceLinearCLM n τ‖ ^ r * ‖g.f τ‖)) := by
                ring
          _ ≤ r.factorial * (Eσ * (CL ^ r * Cg)) := by
                exact mul_le_mul_of_nonneg_left hExpLCg (Nat.cast_nonneg _)
          _ = Eσ * Cderiv := by
                simp [Cderiv]
                ring
      · have hzero_fun :=
          section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport
            n r g hτ_supp
        have hzero : G τ = 0 := by
          simpa [G] using congrFun hzero_fun σ
        calc
          ‖G τ‖ = 0 := by simp [hzero]
          _ ≤ Eσ * Cderiv := mul_nonneg hE_nonneg hCderiv_nonneg
    · rw [Set.indicator_of_notMem hτK]
      have hnot_tsupport :
          τ ∉ tsupport (g.f : (Fin n → ℝ) → ℂ) := by
        intro hτ_supp
        exact hτK (by simpa [Kτ] using hR_supp hτ_supp)
      have hzero_fun :=
        section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport
          n r g hnot_tsupport
      have hzero : G τ = 0 := by
        simpa [G] using congrFun hzero_fun σ
      simp [hzero]
  have hcandidate_norm :
      ‖section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ‖ ≤
        Eσ * M := by
    calc
      ‖section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ‖ =
          ‖∫ τ : Fin n → ℝ, G τ‖ := by
            simp [section43IteratedLaplaceRaw_iteratedFDerivCandidate, G]
      _ ≤ ∫ τ : Fin n → ℝ, ‖G τ‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ τ : Fin n → ℝ,
            Eσ * Set.indicator Kτ (fun _ : Fin n → ℝ => Cderiv) τ := by
          exact MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun τ => norm_nonneg (G τ))
            hbound_int
            (Filter.Eventually.of_forall hpoint)
      _ = Eσ * M := by
          rw [MeasureTheory.integral_const_mul]
  have htime :
      (1 + ‖σ‖) ^ s * Eσ ≤ Ct := by
    simpa [Eσ] using hCt_bound σ hσ
  calc
    (1 + ‖σ‖) ^ s *
        ‖iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ‖ =
        (1 + ‖σ‖) ^ s *
          ‖section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ‖ := by
          rw [section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate]
    _ ≤ (1 + ‖σ‖) ^ s * (Eσ * M) := by
          exact mul_le_mul_of_nonneg_left hcandidate_norm (pow_nonneg (by positivity) s)
    _ = ((1 + ‖σ‖) ^ s * Eσ) * M := by ring
    _ ≤ Ct * M := by
          exact mul_le_mul_of_nonneg_right htime hM_nonneg
    _ = C := rfl

/-- A finite-time ambient Schwartz representative of the multitime
one-sided Laplace transform, modulo equality on the closed positive orthant. -/
def section43IteratedLaplaceRepresentative
    (n : ℕ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (Φ : SchwartzMap (Fin n → ℝ) ℂ) : Prop :=
  ∀ σ : Fin n → ℝ, σ ∈ section43TimePositiveRegion n →
    Φ σ = section43IteratedLaplaceRaw n g σ

/-- Ambient Schwartz representative obtained by cutting off the raw multitime
Laplace scalar on the positive time orthant. -/
noncomputable def section43IteratedLaplaceSchwartzRepresentative
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  schwartzMap_of_temperate_mul_rapid_on_derivSupport
    (χ := section43TimePositiveCutoff n)
    (F := section43IteratedLaplaceRaw n g)
    (S := section43TimePositiveThickening n 1)
    (section43TimePositiveCutoff_hasTemperateGrowth n)
    (fun r σ hne =>
      section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
        (n := n) (r := r) (τ := σ) hne)
    (section43IteratedLaplaceRaw_contDiff n g)
    (by
      intro r s
      exact section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
        n r s g)

/-- On the closed positive orthant, the cutoff Schwartz representative agrees
with the raw multitime Laplace scalar. -/
theorem section43IteratedLaplaceSchwartzRepresentative_apply_of_mem
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n)
    {σ : Fin n → ℝ} (hσ : σ ∈ section43TimePositiveRegion n) :
    section43IteratedLaplaceSchwartzRepresentative n g σ =
      section43IteratedLaplaceRaw n g σ := by
  change section43TimePositiveCutoff n σ *
      section43IteratedLaplaceRaw n g σ =
    section43IteratedLaplaceRaw n g σ
  rw [section43TimePositiveCutoff_eq_one_of_mem hσ]
  simp

/-- Every compact strict-positive finite-time source has an ambient Schwartz
representative of its multitime one-sided Laplace transform. -/
theorem exists_section43IteratedLaplaceRepresentative
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ Φ : SchwartzMap (Fin n → ℝ) ℂ,
      section43IteratedLaplaceRepresentative n g Φ :=
  ⟨section43IteratedLaplaceSchwartzRepresentative n g, by
    intro σ hσ
    exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ⟩

/-- The compact strict-positive multitime Laplace transform, valued in the
finite-time positive-energy quotient. -/
noncomputable def section43IteratedLaplaceCompactTransform
    (n : ℕ) :
    Section43CompactStrictPositiveTimeSource n →
      Section43TimePositiveComponent n :=
  fun g =>
    section43TimePositiveQuotientMap n
      (Classical.choose (exists_section43IteratedLaplaceRepresentative n g))

theorem section43IteratedLaplaceCompactTransform_choose_spec
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    section43IteratedLaplaceRepresentative n g
      (Classical.choose (exists_section43IteratedLaplaceRepresentative n g)) :=
  Classical.choose_spec (exists_section43IteratedLaplaceRepresentative n g)

/-- Any representative of the raw multitime Laplace scalar gives the same
compact transform quotient class. -/
theorem section43IteratedLaplaceCompactTransform_eq_quotient
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (Φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hΦ : section43IteratedLaplaceRepresentative n g Φ) :
    section43IteratedLaplaceCompactTransform n g =
      section43TimePositiveQuotientMap n Φ := by
  dsimp [section43IteratedLaplaceCompactTransform]
  apply section43TimePositiveQuotientMap_eq_of_eqOn_region
  intro σ hσ
  calc
    Classical.choose (exists_section43IteratedLaplaceRepresentative n g) σ
        = section43IteratedLaplaceRaw n g σ :=
          section43IteratedLaplaceCompactTransform_choose_spec n g σ hσ
    _ = Φ σ := (hΦ σ hσ).symm

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

/-- For product sources, the compact multitime transform is represented by the
product tensor of the one-dimensional compact Laplace representatives. -/
theorem section43IteratedLaplaceCompactTransform_productSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    section43IteratedLaplaceCompactTransform n (section43TimeProductSource gs) =
      section43TimePositiveQuotientMap n
        (section43TimeProductTensor
          (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
  section43IteratedLaplaceCompactTransform_eq_quotient
    n (section43TimeProductSource gs)
    (section43TimeProductTensor
      (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
    (section43TimeProductTensor_oneSidedLaplaceRepresentative gs)

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
