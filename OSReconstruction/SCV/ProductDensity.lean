/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import GeneralResults.SchwartzProducts
import OSReconstruction.SCV.ComplexSchwartz
import OSReconstruction.SCV.DistributionalEOWProductKernel
import OSReconstruction.SCV.SchwartzExternalProduct

/-!
# Product-Density Infrastructure for the Theorem-2 Route

This file starts the pure-SCV product-density proof by connecting mixed
complex/real tests to flat real coordinate blocks.  The remaining density
argument will use `GaussianField.productHermite_schwartz_dense` on the flat
domain and the complex decomposition from `SCV.ComplexSchwartz`.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

/-- The one-dimensional real Hermite basis used by GaussianField's product
Hermite density theorem, with the generic Schwartz Dynin-Mityagin instance made
explicit so it matches `GaussianField.productHermite_schwartz_dense`. -/
def realHermiteBasis (k : ℕ) : SchwartzMap ℝ ℝ :=
  @GaussianField.DyninMityaginSpace.basis (SchwartzMap ℝ ℝ) _ _ _ _ _
    (GaussianField.schwartz_dyninMityaginSpace (D := ℝ)) k

/-- Constant Schwartz functions on a subsingleton normed domain. -/
def singletonConstantSchwartz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    (c : ℂ) : SchwartzMap E ℂ where
  toFun := fun _ => c
  smooth' := contDiff_const
  decay' := by
    intro k n
    refine ⟨‖c‖, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim x 0
    subst x
    by_cases hn : n = 0
    · subst n
      cases k <;> simp
    · rw [iteratedFDeriv_const_of_ne hn]
      simp

@[simp]
theorem singletonConstantSchwartz_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    (c : ℂ) (x : E) :
    singletonConstantSchwartz (E := E) c x = c := rfl

/-- Pull a flat Schwartz test on fiber-first real coordinates back to the mixed
complex-chart/fiber domain. -/
def flatMixedCLM (m : ℕ) :
    SchwartzMap (Fin (m + m * 2) → ℝ) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedChartFiberFirstCLE m)

/-- A mixed continuous linear functional transported to the flat fiber-first
coordinate domain. -/
def flattenMixedFunctional (m : ℕ)
    (L : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ) :
    SchwartzMap (Fin (m + m * 2) → ℝ) ℂ →L[ℂ] ℂ :=
  L.comp (flatMixedCLM m)

/-- Product tests on a flat finite append domain, with the first block written
first in the function argument. -/
def twoBlockProductSchwartz {m n : ℕ}
    (B : SchwartzMap (Fin m → ℝ) ℂ)
    (A : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Fin (m + n) → ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finAppendCLE m n).symm)
    (schwartzExternalProduct B A)

@[simp]
theorem finAppendCLE_symm_append {m n : ℕ}
    (t : Fin m → ℝ) (u : Fin n → ℝ) :
    (finAppendCLE m n).symm (Fin.append t u) = (t, u) := by
  apply (finAppendCLE m n).injective
  ext k
  rw [ContinuousLinearEquiv.apply_symm_apply]
  refine Fin.addCases (motive := fun k =>
    Fin.append t u k = finAppendCLE m n (t, u) k) ?_ ?_ k
  · intro i
    simp [Fin.append]
  · intro i
    simp [Fin.append]

@[simp]
theorem finAppendCLE_append_symm {m n : ℕ}
    (x : Fin (m + n) → ℝ) :
    Fin.append ((finAppendCLE m n).symm x).1 ((finAppendCLE m n).symm x).2 = x := by
  have h := (ContinuousLinearEquiv.apply_symm_apply (finAppendCLE m n) x)
  ext k
  refine Fin.addCases (motive := fun k =>
    Fin.append ((finAppendCLE m n).symm x).1 ((finAppendCLE m n).symm x).2 k = x k)
    ?_ ?_ k
  · intro i
    simpa [Fin.append] using congrFun h (Fin.castAdd n i)
  · intro i
    simpa [Fin.append] using congrFun h (Fin.natAdd m i)

@[simp]
theorem twoBlockProductSchwartz_apply {m n : ℕ}
    (B : SchwartzMap (Fin m → ℝ) ℂ)
    (A : SchwartzMap (Fin n → ℝ) ℂ)
    (t : Fin m → ℝ) (u : Fin n → ℝ) :
    twoBlockProductSchwartz B A (Fin.append t u) = B t * A u := by
  simp [twoBlockProductSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Real-valued flat block products embedded into complex Schwartz functions are
the complex two-block products of the embedded factors. -/
theorem schwartzOfRealCLM_eq_twoBlockProduct_of_forall_append
    {m n : ℕ}
    (F : SchwartzMap (Fin (m + n) → ℝ) ℝ)
    (B : SchwartzMap (Fin m → ℝ) ℝ)
    (A : SchwartzMap (Fin n → ℝ) ℝ)
    (hF : ∀ (t : Fin m → ℝ) (u : Fin n → ℝ),
      F (Fin.append t u) = B t * A u) :
    schwartzOfRealCLM F =
      twoBlockProductSchwartz (schwartzOfRealCLM B) (schwartzOfRealCLM A) := by
  ext x
  let p := (finAppendCLE m n).symm x
  have hx : x = Fin.append p.1 p.2 := (finAppendCLE_append_symm x).symm
  rw [hx]
  simp [hF]

/-- A one-dimensional Hermite product on `Fin (m+n) → ℝ` splits into the
head block and tail block product functions. -/
theorem exists_hermite_twoBlockFactors
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ks : Fin (m + n) → ℕ) :
    ∃ (B : SchwartzMap (Fin m → ℝ) ℝ)
      (A : SchwartzMap (Fin n → ℝ) ℝ),
      (∀ t : Fin m → ℝ,
        B t = ∏ i : Fin m,
          realHermiteBasis (ks (Fin.castAdd n i)) (t i)) ∧
      (∀ u : Fin n → ℝ,
        A u = ∏ j : Fin n,
          realHermiteBasis (ks (Fin.natAdd m j)) (u j)) ∧
      ∀ (F : SchwartzMap (Fin (m + n) → ℝ) ℝ),
        (∀ x : Fin (m + n) → ℝ,
          F x = ∏ k : Fin (m + n),
            realHermiteBasis (ks k) (x k)) →
        ∀ (t : Fin m → ℝ) (u : Fin n → ℝ),
          F (Fin.append t u) = B t * A u := by
  obtain ⟨B, hB⟩ := GaussianField.schwartzProductTensor_schwartz
    (D := ℝ) m hm
    (fun i : Fin m =>
      realHermiteBasis (ks (Fin.castAdd n i)))
  obtain ⟨A, hA⟩ := GaussianField.schwartzProductTensor_schwartz
    (D := ℝ) n hn
    (fun j : Fin n =>
      realHermiteBasis (ks (Fin.natAdd m j)))
  refine ⟨B, A, hB, hA, ?_⟩
  intro F hF t u
  rw [hF, Fin.prod_univ_add, hB, hA]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [Fin.append]
  · apply Finset.prod_congr rfl
    intro j _
    simp [Fin.append]

/-- The flat two-block product is exactly the mixed tensor product after pulling
back along the checked fiber-first mixed chart. -/
theorem flatTwoBlockProduct_eq_mixedProduct
    {m : ℕ}
    (A : SchwartzMap (Fin (m * 2) → ℝ) ℂ)
    (B : SchwartzMap (Fin m → ℝ) ℂ) :
    flatMixedCLM m
      (twoBlockProductSchwartz (m := m) (n := m * 2) B A) =
    schwartzTensorProduct₂
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (complexChartRealFlattenCLE m)) A)
      B := by
  ext p
  rcases p with ⟨z, t⟩
  simp [flatMixedCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    mixedChartFiberFirstCLE_apply_finAppend, schwartzTensorProduct₂_apply, mul_comm]

/-- A complex continuous linear functional on the flat fiber-first domain is
zero if it vanishes on all two-block product tests in a positive split. -/
theorem flatComplexCLM_zero_of_zero_on_twoBlockProducts_of_pos
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (Lflat : SchwartzMap (Fin (p + q) → ℝ) ℂ →L[ℂ] ℂ)
    (hL : ∀ (G : SchwartzMap (Fin p → ℝ) ℂ)
        (ξ : SchwartzMap (Fin q → ℝ) ℂ),
      Lflat (twoBlockProductSchwartz G ξ) = 0) :
    Lflat = 0 := by
  let Lre : SchwartzMap (Fin (p + q) → ℝ) ℝ →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((Lflat.restrictScalars ℝ).comp schwartzOfRealCLM)
  let Lim : SchwartzMap (Fin (p + q) → ℝ) ℝ →L[ℝ] ℝ :=
    Complex.imCLM.comp
      ((Lflat.restrictScalars ℝ).comp schwartzOfRealCLM)
  have hp_one : 1 ≤ p := by omega
  have hq_one : 1 ≤ q := by omega
  have hre : Lre = 0 := by
    apply GaussianField.productHermite_schwartz_dense (D := ℝ) (p + q) (by omega)
    intro ks F hF
    obtain ⟨G, ξ, _hG, _hξ, hsplit⟩ :=
      exists_hermite_twoBlockFactors (m := p) (n := q) hp_one hq_one ks
    have hF' : ∀ x : Fin (p + q) → ℝ,
        F x = ∏ k : Fin (p + q), realHermiteBasis (ks k) (x k) := by
      simpa [realHermiteBasis] using hF
    have hprod :
        schwartzOfRealCLM F =
          twoBlockProductSchwartz (m := p) (n := q)
            (schwartzOfRealCLM G) (schwartzOfRealCLM ξ) :=
      schwartzOfRealCLM_eq_twoBlockProduct_of_forall_append F G ξ (hsplit F hF')
    change (Lflat (schwartzOfRealCLM F)).re = 0
    rw [hprod]
    simpa using
      congrArg Complex.re (hL (schwartzOfRealCLM G) (schwartzOfRealCLM ξ))
  have him : Lim = 0 := by
    apply GaussianField.productHermite_schwartz_dense (D := ℝ) (p + q) (by omega)
    intro ks F hF
    obtain ⟨G, ξ, _hG, _hξ, hsplit⟩ :=
      exists_hermite_twoBlockFactors (m := p) (n := q) hp_one hq_one ks
    have hF' : ∀ x : Fin (p + q) → ℝ,
        F x = ∏ k : Fin (p + q), realHermiteBasis (ks k) (x k) := by
      simpa [realHermiteBasis] using hF
    have hprod :
        schwartzOfRealCLM F =
          twoBlockProductSchwartz (m := p) (n := q)
            (schwartzOfRealCLM G) (schwartzOfRealCLM ξ) :=
      schwartzOfRealCLM_eq_twoBlockProduct_of_forall_append F G ξ (hsplit F hF')
    change (Lflat (schwartzOfRealCLM F)).im = 0
    rw [hprod]
    simpa using
      congrArg Complex.im (hL (schwartzOfRealCLM G) (schwartzOfRealCLM ξ))
  ext F
  let R := (complexSchwartzDecomposeCLE F).1
  let I := (complexSchwartzDecomposeCLE F).2
  have hdecomp :
      F = schwartzOfRealCLM R + (Complex.I : ℂ) • schwartzOfRealCLM I := by
    exact (complexSchwartzDecomposeCLE.symm_apply_apply F).symm
  have hR : Lflat (schwartzOfRealCLM R) = 0 := by
    apply Complex.ext
    · change Lre R = 0
      rw [hre]
      rfl
    · change Lim R = 0
      rw [him]
      rfl
  have hI : Lflat (schwartzOfRealCLM I) = 0 := by
    apply Complex.ext
    · change Lre I = 0
      rw [hre]
      rfl
    · change Lim I = 0
      rw [him]
      rfl
  rw [hdecomp, map_add, map_smul, hR, hI]
  simp

/-- A complex continuous linear functional on the flat fiber-first domain is
zero if it vanishes on all two-block product tests. -/
theorem flatComplexCLM_zero_of_zero_on_twoBlockProducts
    {m : ℕ} (hm : 0 < m)
    (Lflat : SchwartzMap (Fin (m + m * 2) → ℝ) ℂ →L[ℂ] ℂ)
    (hL : ∀ (A : SchwartzMap (Fin (m * 2) → ℝ) ℂ)
        (B : SchwartzMap (Fin m → ℝ) ℂ),
      Lflat (twoBlockProductSchwartz (m := m) (n := m * 2) B A) = 0) :
    Lflat = 0 := by
  exact flatComplexCLM_zero_of_zero_on_twoBlockProducts_of_pos
    (p := m) (q := m * 2) hm (by omega) Lflat (by
      intro B A
      exact hL A B)

/-- For positive block dimensions, flat two-block product tests have dense
complex span. -/
theorem flatTwoBlockProductDense_of_pos
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Dense ((Submodule.span ℂ
      {F : SchwartzMap (Fin (p + q) → ℝ) ℂ |
        ∃ G ξ, F = twoBlockProductSchwartz G ξ}) :
      Set (SchwartzMap (Fin (p + q) → ℝ) ℂ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hM
  let M : Submodule ℂ (SchwartzMap (Fin (p + q) → ℝ) ℂ) :=
    Submodule.span ℂ
      {F : SchwartzMap (Fin (p + q) → ℝ) ℂ |
        ∃ G ξ, F = twoBlockProductSchwartz G ξ}
  have hx : ∃ x : SchwartzMap (Fin (p + q) → ℝ) ℂ,
      x ∉ M.topologicalClosure := by
    by_contra hx
    apply hM
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx'
    exact hx ⟨x, hx'⟩
  have hconv : Convex ℝ
      (M.topologicalClosure :
        Set (SchwartzMap (Fin (p + q) → ℝ) ℂ)) := by
    simpa using (M.topologicalClosure.restrictScalars ℝ).convex
  rcases hx with ⟨x, hx⟩
  obtain ⟨f, u, hleft, hright⟩ :=
    RCLike.geometric_hahn_banach_closed_point
      (𝕜 := ℂ)
      (E := SchwartzMap (Fin (p + q) → ℝ) ℂ)
      (x := x)
      (s := (M.topologicalClosure :
        Set (SchwartzMap (Fin (p + q) → ℝ) ℂ)))
      hconv M.isClosed_topologicalClosure hx
  have hu_pos : 0 < u := by
    have hzero := hleft 0 M.topologicalClosure.zero_mem
    simpa using hzero
  have hre_zero :
      ∀ y ∈ M.topologicalClosure, (f y).re = 0 := by
    intro y hy
    by_contra hre
    let r : ℝ := (u + 1) / (f y).re
    have hlt := hleft ((r : ℂ) • y) (M.topologicalClosure.smul_mem (r : ℂ) hy)
    have hreval : (f ((r : ℂ) • y)).re = u + 1 := by
      calc
        (f ((r : ℂ) • y)).re = r * (f y).re := by
          simp [r, mul_comm]
        _ = u + 1 := by
          dsimp [r]
          field_simp [hre]
    have : ¬ u + 1 < u := by linarith
    exact this (hreval ▸ hlt)
  have hvanish :
      ∀ y ∈ M.topologicalClosure, f y = 0 := by
    intro y hy
    have hre : (f y).re = 0 := hre_zero y hy
    have hIy_re : (f ((Complex.I : ℂ) • y)).re = 0 := by
      exact hre_zero ((Complex.I : ℂ) • y) (M.topologicalClosure.smul_mem Complex.I hy)
    have him : (f y).im = 0 := by
      have htmp : -(f y).im = 0 := by
        simpa [ContinuousLinearMap.map_smul, mul_comm, mul_left_comm, mul_assoc] using hIy_re
      linarith
    exact Complex.ext hre him
  have hfS : ∀ y ∈ M, f y = 0 := by
    intro y hy
    exact hvanish y (subset_closure hy)
  have hf_prod :
      ∀ (G : SchwartzMap (Fin p → ℝ) ℂ)
        (ξ : SchwartzMap (Fin q → ℝ) ℂ),
        f (twoBlockProductSchwartz G ξ) = 0 := by
    intro G ξ
    exact hfS _ (Submodule.subset_span ⟨G, ξ, rfl⟩)
  have hf_zero : f = 0 :=
    flatComplexCLM_zero_of_zero_on_twoBlockProducts_of_pos hp hq f hf_prod
  have : ¬ u < (0 : ℝ) := not_lt_of_ge hu_pos.le
  apply this
  simpa [hf_zero] using hright

/-- A mixed-chart continuous linear functional is zero if it vanishes on all
standard mixed product tensors. -/
theorem mixedProductCLM_zero_of_zero_on_productTensor
    {m : ℕ} (hm : 0 < m)
    (L : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hL : ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
      L (schwartzTensorProduct₂ φ ψ) = 0) :
    L = 0 := by
  have hflat :
      flattenMixedFunctional m L = 0 :=
    flatComplexCLM_zero_of_zero_on_twoBlockProducts hm
      (flattenMixedFunctional m L) (by
        intro A B
        change L (flatMixedCLM m
          (twoBlockProductSchwartz (m := m) (n := m * 2) B A)) = 0
        rw [flatTwoBlockProduct_eq_mixedProduct]
        exact hL _ _)
  ext F
  have harg := congrArg (fun T : SchwartzMap (Fin (m + m * 2) → ℝ) ℂ →L[ℂ] ℂ =>
      T ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (mixedChartFiberFirstCLE m).symm) F)) hflat
  simpa [flattenMixedFunctional, flatMixedCLM, ContinuousLinearMap.comp_apply] using harg

/-- For positive `m`, mixed product tensors have dense complex span. -/
theorem ProductTensorDense_of_pos {m : ℕ} (hm : 0 < m) :
    ProductTensorDense m := by
  rw [ProductTensorDense, Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hM
  let M := productTensorSpan m
  have hx : ∃ x : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
      x ∉ M.topologicalClosure := by
    by_contra hx
    apply hM
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx'
    exact hx ⟨x, hx'⟩
  have hconv : Convex ℝ
      (M.topologicalClosure :
        Set (SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)) := by
    simpa using (M.topologicalClosure.restrictScalars ℝ).convex
  rcases hx with ⟨x, hx⟩
  obtain ⟨f, u, hleft, hright⟩ :=
    RCLike.geometric_hahn_banach_closed_point
      (𝕜 := ℂ)
      (E := SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
      (x := x)
      (s := (M.topologicalClosure :
        Set (SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)))
      hconv M.isClosed_topologicalClosure hx
  have hu_pos : 0 < u := by
    have hzero := hleft 0 M.topologicalClosure.zero_mem
    simpa using hzero
  have hre_zero :
      ∀ y ∈ M.topologicalClosure, (f y).re = 0 := by
    intro y hy
    by_contra hre
    let r : ℝ := (u + 1) / (f y).re
    have hlt := hleft ((r : ℂ) • y) (M.topologicalClosure.smul_mem (r : ℂ) hy)
    have hreval : (f ((r : ℂ) • y)).re = u + 1 := by
      calc
        (f ((r : ℂ) • y)).re = r * (f y).re := by
          simp [r, mul_comm]
        _ = u + 1 := by
          dsimp [r]
          field_simp [hre]
    have : ¬ u + 1 < u := by linarith
    exact this (hreval ▸ hlt)
  have hvanish :
      ∀ y ∈ M.topologicalClosure, f y = 0 := by
    intro y hy
    have hre : (f y).re = 0 := hre_zero y hy
    have hIy_re : (f ((Complex.I : ℂ) • y)).re = 0 := by
      exact hre_zero ((Complex.I : ℂ) • y) (M.topologicalClosure.smul_mem Complex.I hy)
    have him : (f y).im = 0 := by
      have htmp : -(f y).im = 0 := by
        simpa [ContinuousLinearMap.map_smul, mul_comm, mul_left_comm, mul_assoc] using hIy_re
      linarith
    exact Complex.ext hre him
  have hfS : ∀ y ∈ M, f y = 0 := by
    intro y hy
    exact hvanish y (subset_closure hy)
  have hf_prod :
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        f (schwartzTensorProduct₂ φ ψ) = 0 := by
    intro φ ψ
    exact hfS _ (Submodule.subset_span ⟨φ, ψ, rfl⟩)
  have hf_zero : f = 0 :=
    mixedProductCLM_zero_of_zero_on_productTensor hm f hf_prod
  have : ¬ u < (0 : ℝ) := not_lt_of_ge hu_pos.le
  apply this
  simpa [hf_zero] using hright

/-- The zero-dimensional mixed product tensor span is already the whole
Schwartz space, since the domain is a singleton. -/
theorem ProductTensorDense_zero : ProductTensorDense 0 := by
  rw [ProductTensorDense, Submodule.dense_iff_topologicalClosure_eq_top]
  rw [Submodule.eq_top_iff']
  intro F
  let φ : SchwartzMap (ComplexChartSpace 0) ℂ :=
    singletonConstantSchwartz (F (0, 0))
  let ψ : SchwartzMap (Fin 0 → ℝ) ℂ :=
    singletonConstantSchwartz 1
  have hprod : F = schwartzTensorProduct₂ φ ψ := by
    ext p
    have hp : p = ((0 : ComplexChartSpace 0), (0 : Fin 0 → ℝ)) :=
      Subsingleton.elim p _
    subst p
    simp [φ, ψ, schwartzTensorProduct₂_apply]
  exact subset_closure (Submodule.subset_span ⟨φ, ψ, hprod⟩)

/-- Mixed product tensors have dense complex span for every `m`. -/
theorem ProductTensorDense_all (m : ℕ) : ProductTensorDense m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ProductTensorDense_zero
  · exact ProductTensorDense_of_pos hm

/-- Product-kernel descent with the mixed product-density theorem discharged. -/
theorem translationCovariantProductKernel_descends
    {m : ℕ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hcov : ProductKernelRealTranslationCovariantGlobal K)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : ∫ t : Fin m → ℝ, η t = 1) :
    ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        K (schwartzTensorProduct₂ φ ψ) = Hdist (realConvolutionTest φ ψ) :=
  translationCovariantProductKernel_descends_of_productTensorDense
    (ProductTensorDense_all m) K hcov η hη

end SCV
