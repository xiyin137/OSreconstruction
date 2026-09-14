/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import GeneralResults.SchwartzProducts
import OSReconstruction.SCV.ComplexSchwartz
import OSReconstruction.SCV.DistributionalEOWProductKernel
import OSReconstruction.SCV.SchwartzExternalProduct










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

end SCV
