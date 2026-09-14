/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import OSReconstruction.ComplexLieGroups.LorentzLieGroup
import OSReconstruction.ComplexLieGroups.SOConnected


































noncomputable section

open Complex Topology Matrix LorentzLieGroup

variable {d : ℕ}



/-- The complex Lorentz group SO⁺(1,d;ℂ): complex matrices preserving the
    Minkowski metric with determinant 1.

    Over ℂ, this group is already connected (unlike the real Lorentz group
    which has 4 connected components). No separate orthochronous condition
    is needed. -/
structure ComplexLorentzGroup (d : ℕ) where
  /-- The matrix Λ ∈ M_{(d+1)×(d+1)}(ℂ) -/
  val : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  /-- Preserves Minkowski metric: ΛᵀηΛ = η, componentwise.
      Σ_α η(α) · Λ(α,μ) · Λ(α,ν) = η(μ) · δ_{μν} -/
  metric_preserving : ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * val α μ * val α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0
  /-- Proper: det(Λ) = 1 -/
  proper : val.det = 1

namespace ComplexLorentzGroup



/-- Topology from the embedding into complex matrices. -/
instance instTopologicalSpace : TopologicalSpace (ComplexLorentzGroup d) :=
  TopologicalSpace.induced ComplexLorentzGroup.val inferInstance

/-- The `val` projection is continuous. -/
theorem continuous_val :
    Continuous (ComplexLorentzGroup.val : ComplexLorentzGroup d →
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  continuous_induced_dom

/-- Matrix entries are continuous. -/
theorem continuous_entry (μ ν : Fin (d + 1)) :
    Continuous (fun Λ : ComplexLorentzGroup d => Λ.val μ ν) :=
  (continuous_apply_apply μ ν).comp continuous_val



/-- The complex Minkowski metric matrix η_ℂ = diag(-1, +1, ..., +1). -/
def ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => (minkowskiSignature d i : ℂ))

theorem ηℂ_sq : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * ηℂ = 1 := by
  simp only [ηℂ, Matrix.diagonal_mul_diagonal]
  ext i j; simp [Matrix.diagonal, Matrix.one_apply, minkowskiSignature]
  split_ifs <;> push_cast <;> ring

theorem ηℂ_transpose :
    (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = ηℂ := by
  simp [ηℂ, Matrix.diagonal_transpose]

/-- The componentwise metric condition is equivalent to the matrix equation Λᵀ η Λ = η. -/
theorem metric_preserving_matrix (Λ : ComplexLorentzGroup d) :
    Λ.val.transpose * ηℂ * Λ.val = ηℂ := by
  ext μ ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ηℂ, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  convert Λ.metric_preserving μ ν using 1
  apply Finset.sum_congr rfl; intro α _; ring

/-- Recover the componentwise condition from the matrix equation. -/
theorem of_metric_preserving_matrix {M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (h : M.transpose * ηℂ * M = ηℂ) :
    ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * M α μ * M α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  have := congr_fun (congr_fun h μ) ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ηℂ, Matrix.diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  convert this using 1
  apply Finset.sum_congr rfl; intro α _; ring



/-- The identity matrix is in SO⁺(1,d;ℂ). -/
def one : ComplexLorentzGroup d where
  val := 1
  metric_preserving := by
    intro μ ν
    simp only [Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [Finset.sum_ite_eq', minkowskiSignature]
    · apply Finset.sum_eq_zero; intro α _
      by_cases hα : α = μ <;> simp [hα, h]
  proper := by simp

/-- The product of two elements of SO⁺(1,d;ℂ) is in SO⁺(1,d;ℂ). -/
def mul (Λ₁ Λ₂ : ComplexLorentzGroup d) : ComplexLorentzGroup d where
  val := Λ₁.val * Λ₂.val
  metric_preserving := by
    -- (Λ₁Λ₂)ᵀ η (Λ₁Λ₂) = Λ₂ᵀ (Λ₁ᵀ η Λ₁) Λ₂ = Λ₂ᵀ η Λ₂ = η
    apply of_metric_preserving_matrix
    rw [Matrix.transpose_mul]
    calc Λ₂.val.transpose * Λ₁.val.transpose * ηℂ * (Λ₁.val * Λ₂.val)
        = Λ₂.val.transpose * (Λ₁.val.transpose * ηℂ * Λ₁.val) * Λ₂.val := by
          simp only [Matrix.mul_assoc]
      _ = Λ₂.val.transpose * ηℂ * Λ₂.val := by rw [metric_preserving_matrix Λ₁]
      _ = ηℂ := metric_preserving_matrix Λ₂
  proper := by
    show (Λ₁.val * Λ₂.val).det = 1
    rw [Matrix.det_mul, Λ₁.proper, Λ₂.proper, mul_one]

instance instGroup : Group (ComplexLorentzGroup d) where
  mul := mul
  one := one
  inv Λ := {
    val := ηℂ * Λ.val.transpose * ηℂ
    metric_preserving := by
      apply of_metric_preserving_matrix
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ηℂ_transpose]
      have hη := ηℂ_sq (d := d)
      have hΛ := metric_preserving_matrix Λ
      -- Need: Λ * η * Λᵀ = η (from Λ * (η Λᵀ η) = 1 and η² = 1)
      have inv_mul : (ηℂ * Λ.val.transpose * ηℂ) * Λ.val = 1 := by
        calc ηℂ * Λ.val.transpose * ηℂ * Λ.val
            = ηℂ * (Λ.val.transpose * ηℂ * Λ.val) := by simp only [Matrix.mul_assoc]
          _ = ηℂ * ηℂ := by rw [hΛ]
          _ = 1 := hη
      have mul_inv : Λ.val * (ηℂ * Λ.val.transpose * ηℂ) = 1 :=
        mul_eq_one_comm.mpr inv_mul
      have hΛηΛt : Λ.val * ηℂ * Λ.val.transpose = ηℂ := by
        have h1 : Λ.val * ηℂ * Λ.val.transpose * ηℂ = 1 := by
          calc Λ.val * ηℂ * Λ.val.transpose * ηℂ
              = Λ.val * (ηℂ * Λ.val.transpose * ηℂ) := by simp only [Matrix.mul_assoc]
            _ = 1 := mul_inv
        calc Λ.val * ηℂ * Λ.val.transpose
            = Λ.val * ηℂ * Λ.val.transpose * 1 := by rw [Matrix.mul_one]
          _ = Λ.val * ηℂ * Λ.val.transpose * (ηℂ * ηℂ) := by rw [hη]
          _ = (Λ.val * ηℂ * Λ.val.transpose * ηℂ) * ηℂ := by simp only [Matrix.mul_assoc]
          _ = 1 * ηℂ := by rw [h1]
          _ = ηℂ := Matrix.one_mul _
      calc ηℂ * (Λ.val * ηℂ) * ηℂ * (ηℂ * Λ.val.transpose * ηℂ)
          = ηℂ * Λ.val * (ηℂ * ηℂ) * (ηℂ * Λ.val.transpose * ηℂ) := by
            simp only [Matrix.mul_assoc]
        _ = ηℂ * Λ.val * (ηℂ * Λ.val.transpose * ηℂ) := by rw [hη, Matrix.mul_one]
        _ = ηℂ * (Λ.val * ηℂ * Λ.val.transpose) * ηℂ := by simp only [Matrix.mul_assoc]
        _ = ηℂ * ηℂ * ηℂ := by rw [hΛηΛt]
        _ = 1 * ηℂ := by rw [hη]
        _ = ηℂ := Matrix.one_mul _
    proper := by
      show (ηℂ * Λ.val.transpose * ηℂ).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Λ.proper, mul_one]
      have : (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det *
          (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).det = 1 := by
        have := congr_arg Matrix.det (ηℂ_sq (d := d))
        rwa [Matrix.det_mul, Matrix.det_one] at this
      exact this
  }
  mul_assoc a b c := by
    show mul (mul a b) c = mul a (mul b c)
    cases a; cases b; cases c
    simp only [mul, Matrix.mul_assoc]
  one_mul a := by
    show mul one a = a
    cases a; simp only [mul, one, Matrix.one_mul]
  mul_one a := by
    show mul a one = a
    cases a; simp only [mul, one, Matrix.mul_one]
  inv_mul_cancel := by
    intro a
    show mul ⟨ηℂ * a.val.transpose * ηℂ, _, _⟩ a = one
    cases a with | mk v mp pr =>
    simp only [mul, one]
    congr 1
    calc ηℂ * v.transpose * ηℂ * v
        = ηℂ * (v.transpose * ηℂ * v) := by simp only [Matrix.mul_assoc]
      _ = ηℂ * ηℂ := by
          congr 1
          have : (ComplexLorentzGroup.mk v mp pr).val.transpose * ηℂ *
              (ComplexLorentzGroup.mk v mp pr).val = ηℂ :=
            metric_preserving_matrix ⟨v, mp, pr⟩
          simpa using this
      _ = 1 := ηℂ_sq



instance instContinuousMul : ContinuousMul (ComplexLorentzGroup d) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : ComplexLorentzGroup d × ComplexLorentzGroup d =>
      p.1.val * p.2.val)
    exact (continuous_val.comp continuous_fst).mul
      (continuous_val.comp continuous_snd)

instance instContinuousInv : ContinuousInv (ComplexLorentzGroup d) where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun a : ComplexLorentzGroup d =>
      (ηℂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * a.val.transpose * ηℂ)
    exact ((continuous_const.mul (continuous_val.matrix_transpose)).mul
      continuous_const)

instance instIsTopologicalGroup : IsTopologicalGroup (ComplexLorentzGroup d) :=
  { instContinuousMul, instContinuousInv with }

private theorem isClosed_range_val :
    IsClosed (Set.range (ComplexLorentzGroup.val :
      ComplexLorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) := by
  let metricSet : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    {M | ∀ (μ ν : Fin (d + 1)),
      ∑ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) * M α μ * M α ν =
      if μ = ν then (minkowskiSignature d μ : ℂ) else 0}
  let detSet : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := {M | M.det = 1}
  have hmetric_closed : IsClosed metricSet := by
    let S : Fin (d + 1) → Fin (d + 1) →
        Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
      fun μ ν =>
        {M | ∑ α : Fin (d + 1),
            (minkowskiSignature d α : ℂ) * M α μ * M α ν =
          if μ = ν then (minkowskiSignature d μ : ℂ) else 0}
    have hS_closed : ∀ μ ν, IsClosed (S μ ν) := by
      intro μ ν
      have hcont : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          ∑ α : Fin (d + 1), (minkowskiSignature d α : ℂ) * M α μ * M α ν) := by
        apply continuous_finset_sum Finset.univ
        intro α _
        have hentryμ : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M α μ) :=
          (continuous_apply μ).comp (continuous_apply α)
        have hentryν : Continuous (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M α ν) :=
          (continuous_apply ν).comp (continuous_apply α)
        simpa [mul_assoc] using (continuous_const.mul (hentryμ.mul hentryν))
      exact (isClosed_singleton
          (x := if μ = ν then (minkowskiSignature d μ : ℂ) else 0)).preimage hcont
    have hmetric_eq : metricSet = ⋂ μ : Fin (d + 1), ⋂ ν : Fin (d + 1), S μ ν := by
      ext M
      simp [metricSet, S]
    rw [hmetric_eq]
    exact isClosed_iInter (fun μ => isClosed_iInter (fun ν => hS_closed μ ν))
  have hdet_closed : IsClosed detSet := by
    exact (isClosed_singleton (x := (1 : ℂ))).preimage (continuous_id.matrix_det)
  have h_range_eq :
      Set.range (ComplexLorentzGroup.val :
        ComplexLorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      metricSet ∩ detSet := by
    ext M
    constructor
    · rintro ⟨Λ, rfl⟩
      exact ⟨Λ.metric_preserving, Λ.proper⟩
    · intro hM
      exact ⟨⟨M, hM.1, hM.2⟩, rfl⟩
  simpa [h_range_eq] using hmetric_closed.inter hdet_closed

private theorem isClosedEmbedding_val :
    Topology.IsClosedEmbedding (ComplexLorentzGroup.val :
      ComplexLorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  have hind : Topology.IsInducing (ComplexLorentzGroup.val :
      ComplexLorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := ⟨rfl⟩
  have hinj : Function.Injective (ComplexLorentzGroup.val :
      ComplexLorentzGroup d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    intro x y hxy
    cases x
    cases y
    cases hxy
    rfl
  exact Topology.IsClosedEmbedding.mk ⟨hind, hinj⟩ isClosed_range_val

instance instSigmaCompactSpace : SigmaCompactSpace (ComplexLorentzGroup d) := by
  letI : SecondCountableTopology (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    simpa [Matrix] using
      (inferInstance : SecondCountableTopology
        (Fin (d + 1) → Fin (d + 1) → ℂ))
  letI : LocallyCompactSpace (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    simpa [Matrix] using
      (inferInstance : LocallyCompactSpace
        (Fin (d + 1) → Fin (d + 1) → ℂ))
  exact (isClosedEmbedding_val (d := d)).sigmaCompactSpace



/-- The real restricted Lorentz group embeds into SO⁺(1,d;ℂ)
    by viewing real matrices as complex matrices. -/
def ofReal (Λ : RestrictedLorentzGroup d) : ComplexLorentzGroup d where
  val := fun i j => (Λ.val.val i j : ℂ)
  metric_preserving := by
    intro μ ν
    -- Extract the componentwise real Lorentz condition (with full simplification)
    have h := Λ.val.prop
    have hμν := congr_fun (congr_fun h μ) ν
    simp only [Matrix.mul_apply, Matrix.transpose_apply, minkowskiMatrix,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hμν
    -- hμν : ∑ x, Λ x μ * η x * Λ x ν = if μ = ν then η μ else 0 (over ℝ)
    -- Rewrite each summand to a single ℝ→ℂ cast
    have cast_eq : ∀ α, (minkowskiSignature d α : ℂ) * (↑(Λ.val.val α μ) : ℂ) *
        (↑(Λ.val.val α ν) : ℂ) =
        ((Λ.val.val α μ * minkowskiSignature d α * Λ.val.val α ν : ℝ) : ℂ) := by
      intro α; push_cast; ring
    simp_rw [cast_eq]
    norm_cast
    rw [hμν]
    split_ifs <;> simp
  proper := by
    change (Complex.ofRealHom.mapMatrix Λ.val.val).det = 1
    rw [← RingHom.map_det]
    have hdet : Λ.val.val.det = 1 := Λ.prop.1
    rw [hdet, map_one]

/-- SO(d+1;ℝ) embeds into SO⁺(1,d;ℂ) via Wick rotation conjugation.
    R ↦ W R W⁻¹ where W = diag(i, 1, ..., 1). -/
def ofEuclidean (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.det = 1) (horth : R.transpose * R = 1) :
    ComplexLorentzGroup d where
  val := fun μ ν =>
    let wμ : ℂ := if μ = (0 : Fin (d + 1)) then I else 1
    let wν_inv : ℂ := if ν = (0 : Fin (d + 1)) then -I else 1
    wμ * (R μ ν : ℂ) * wν_inv
  metric_preserving := by
    intro μ ν
    -- Key identity: η(α) · w(α)² = 1 for all α
    -- (For α=0: (-1)·I² = (-1)·(-1) = 1; for α≠0: 1·1² = 1)
    have hw_sq : ∀ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
        (if α = (0 : Fin (d + 1)) then I else 1) ^ 2 = 1 := by
      intro α; simp only [minkowskiSignature]
      split_ifs <;> push_cast <;> simp [Complex.I_sq]
    -- From horth: (Rᵀ R)(μ,ν) = δ(μ,ν), cast to ℂ
    have hRR : ∑ α : Fin (d + 1), (R α μ : ℂ) * (R α ν : ℂ) =
        if μ = ν then 1 else 0 := by
      have h := congr_fun (congr_fun horth μ) ν
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
      have h' : (↑(∑ x : Fin (d + 1), R x μ * R x ν) : ℂ) =
          (if μ = ν then (1 : ℂ) else 0) := by rw [h]; split_ifs <;> simp
      push_cast at h'; exact h'
    -- Transform each summand: factor out w_inv(μ) · w_inv(ν) using hw_sq
    have key : ∀ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
          ((if α = (0 : Fin (d + 1)) then I else 1) * (↑(R α μ) : ℂ) *
            (if μ = (0 : Fin (d + 1)) then -I else 1)) *
          ((if α = (0 : Fin (d + 1)) then I else 1) * (↑(R α ν) : ℂ) *
            (if ν = (0 : Fin (d + 1)) then -I else 1)) =
        (if μ = (0 : Fin (d + 1)) then -I else 1) *
          (if ν = (0 : Fin (d + 1)) then -I else 1) *
          ((↑(R α μ) : ℂ) * (↑(R α ν) : ℂ)) := by
      intro α
      by_cases hα : α = (0 : Fin (d + 1))
      · subst hα
        simp only [minkowskiSignature, ↓reduceIte]; push_cast
        set wμ := (if μ = (0 : Fin (d + 1)) then (-I : ℂ) else 1)
        set wν := (if ν = (0 : Fin (d + 1)) then (-I : ℂ) else 1)
        have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
        linear_combination -(↑(R 0 μ) * ↑(R 0 ν) * wμ * wν) * hI
      · simp only [minkowskiSignature, hα, ↓reduceIte]; push_cast; ring
    simp_rw [key, ← Finset.mul_sum, hRR]
    -- Goal: w_inv(μ) · w_inv(ν) · δ(μ,ν) = if μ = ν then η(μ) else 0
    by_cases h : μ = ν
    · subst h
      simp only [if_true, mul_one, minkowskiSignature]
      split_ifs with h0 <;> push_cast <;> simp [Complex.I_mul_I]
    · simp [if_neg h]
  proper := by
    -- Express val as W · R_ℂ · W⁻¹ where W = diag(I,1,...,1), W⁻¹ = diag(-I,1,...,1)
    -- det(W · R_ℂ · W⁻¹) = det(W) · det(R_ℂ) · det(W⁻¹) = I · 1 · (-I) = 1
    suffices h : Matrix.det (
        Matrix.diagonal (fun i : Fin (d + 1) => if i = (0 : Fin (d + 1)) then I else (1 : ℂ)) *
        Complex.ofRealHom.mapMatrix R *
        Matrix.diagonal (fun i : Fin (d + 1) =>
          if i = (0 : Fin (d + 1)) then -I else (1 : ℂ))) = 1 by
      convert h using 2
      ext μ ν
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal,
        RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [show (Complex.ofRealHom.mapMatrix R).det = (R.det : ℂ) from by
      rw [← RingHom.map_det]; rfl]
    rw [hR]; push_cast; simp only [mul_one, mul_neg, Complex.I_mul_I, neg_neg]

@[simp] theorem one_val' : (1 : ComplexLorentzGroup d).val = 1 := rfl
@[simp] theorem mul_val (Λ₁ Λ₂ : ComplexLorentzGroup d) :
    (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl



/-- Two elements of `ComplexLorentzGroup` with the same matrix are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : ComplexLorentzGroup d}
    (h : Λ₁.val = Λ₂.val) : Λ₁ = Λ₂ := by
  cases Λ₁; cases Λ₂; cases h; rfl

open NormedSpace in
/-- ηℂ as a matrix unit (since ηℂ² = 1). -/
def ηℂ_unit : (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)ˣ where
  val := ηℂ
  inv := ηℂ
  val_inv := ηℂ_sq
  inv_val := ηℂ_sq

/-- The Lie algebra condition: X^T η + η X = 0. -/
def IsInLieAlgebra (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) : Prop :=
  X.transpose * ηℂ + ηℂ * X = 0





/-- Wick rotation matrix W = diag(i, 1, ..., 1). -/
private def W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = (0 : Fin (d + 1)) then I else 1)

/-- Inverse Wick rotation matrix W⁻¹ = diag(-i, 1, ..., 1). -/
private def Winv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = (0 : Fin (d + 1)) then -I else 1)

private theorem W_mul_Winv :
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Winv = 1 := by
  simp only [W, Winv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; split_ifs <;> simp [I_mul_I]

private theorem Winv_mul_W :
    (Winv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * W = 1 := by
  simp only [W, Winv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; split_ifs <;> simp [I_mul_I]

private theorem Winv_sq_eq_eta :
    (Winv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * Winv = ηℂ := by
  simp only [Winv, ηℂ, Matrix.diagonal_mul_diagonal]
  congr 1; ext i; simp only [minkowskiSignature]
  split_ifs <;> push_cast <;> simp [I_mul_I]

private theorem W_transpose_eq :
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = W :=
  Matrix.diagonal_transpose _

private theorem Winv_transpose_eq :
    (Winv : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose = Winv :=
  Matrix.diagonal_transpose _

private theorem W_eta_W :
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * ηℂ * W = 1 := by
  simp only [W, ηℂ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; simp only [minkowskiSignature]
  split_ifs <;> push_cast <;> simp [I_mul_I]

/-- Map from ComplexLorentzGroup to SOComplex via Wick rotation: Λ ↦ W⁻¹ Λ W. -/
def toSOComplex (Λ : ComplexLorentzGroup d) : SOComplex (d + 1) where
  val := Winv * Λ.val * W
  orthogonal := by
    have hWinvSq : ∀ M : Matrix _ _ ℂ,
        (Winv (d := d)) * (Winv * M) = ηℂ * M :=
      fun M => by rw [← Matrix.mul_assoc, Winv_sq_eq_eta]
    have hΛmet : ∀ M : Matrix _ _ ℂ,
        Λ.val.transpose * (ηℂ * (Λ.val * M)) = ηℂ * M := by
      intro M
      calc Λ.val.transpose * (ηℂ * (Λ.val * M))
          = Λ.val.transpose * ηℂ * Λ.val * M := by simp only [Matrix.mul_assoc]
        _ = ηℂ * M := by rw [metric_preserving_matrix Λ]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, W_transpose_eq, Winv_transpose_eq]
    simp only [Matrix.mul_assoc]
    rw [hWinvSq, hΛmet, ← Matrix.mul_assoc, W_eta_W]
  proper := by
    rw [Matrix.det_mul, Matrix.det_mul, Λ.proper, mul_one,
      ← Matrix.det_mul, Winv_mul_W, Matrix.det_one]

/-- Top-left entry is preserved by Wick rotation. -/
theorem toSOComplex_entry_00 (Λ : ComplexLorentzGroup d) :
    (toSOComplex Λ).val 0 0 = Λ.val 0 0 := by
  change ((Winv (d := d)) * Λ.val * (W (d := d))) 0 0 = Λ.val 0 0
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · simp [W, Winv, mul_assoc]
      have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by norm_num
      calc
        -(Complex.I * (Λ.val 0 0 * Complex.I)) = -((Complex.I : ℂ) ^ 2 * Λ.val 0 0) := by
          ring
        _ = -((-1) * Λ.val 0 0) := by simp [hI2]
        _ = Λ.val 0 0 := by ring
    · intro j _ hj
      have hWinv : Winv (d := d) 0 j = 0 := by
        simp [Winv, hj.symm]
      simp [hWinv]
    · simp
  · intro x _ hx
    have hW : W x 0 = 0 := by simp [W, hx]
    simp [hW]
  · simp

/-- Spatial first-column entries of `toSOComplex Λ` are `I` times those of `Λ`. -/
theorem toSOComplex_entry_succ0 (Λ : ComplexLorentzGroup d) (i : Fin d) :
    (toSOComplex Λ).val i.succ 0 = Λ.val i.succ 0 * Complex.I := by
  change ((Winv (d := d)) * Λ.val * (W (d := d))) i.succ 0 =
    Λ.val i.succ 0 * Complex.I
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i.succ]
    · simp [W, Winv]
    · intro j _ hj
      have hWinv : Winv (d := d) i.succ j = 0 := by
        simp [Winv, hj.symm]
      simp [hWinv]
    · simp
  · intro x _ hx
    have hW : W x 0 = 0 := by simp [W, hx]
    simp [hW]
  · simp

/-- Wick rotation preserves the first-column-`e₀` condition. -/
theorem toSOComplex_firstColEqE0_iff (Λ : ComplexLorentzGroup d) :
    (∀ k : Fin (d + 1), (toSOComplex Λ).val k 0 = if k = 0 then 1 else 0) ↔
      (∀ k : Fin (d + 1), Λ.val k 0 = if k = 0 then 1 else 0) := by
  constructor
  · intro h k
    refine Fin.cases ?_ ?_ k
    · simpa [toSOComplex_entry_00] using h 0
    · intro i
      have hi := h i.succ
      have hmul : Λ.val i.succ 0 * Complex.I = 0 := by
        simpa [toSOComplex_entry_succ0, Fin.succ_ne_zero] using hi
      have hzero : Λ.val i.succ 0 = 0 := by
        exact (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
      simpa [Fin.succ_ne_zero] using hzero
  · intro h k
    refine Fin.cases ?_ ?_ k
    · simpa [toSOComplex_entry_00] using h 0
    · intro i
      have hzero : Λ.val i.succ 0 = 0 := by
        simpa [Fin.succ_ne_zero] using h i.succ
      simp [toSOComplex_entry_succ0, Fin.succ_ne_zero, hzero]

/-- Map from SOComplex to ComplexLorentzGroup via inverse Wick rotation: A ↦ W A W⁻¹. -/
def fromSOComplex (A : SOComplex (d + 1)) : ComplexLorentzGroup d where
  val := W * A.val * Winv
  metric_preserving := by
    apply of_metric_preserving_matrix
    have hWηW : ∀ M : Matrix _ _ ℂ,
        (W (d := d)) * (ηℂ * (W * M)) = M := by
      intro M
      calc W * (ηℂ * (W * M))
          = W * ηℂ * W * M := by simp only [Matrix.mul_assoc]
        _ = 1 * M := by rw [W_eta_W]
        _ = M := Matrix.one_mul _
    have hAorth : ∀ M : Matrix _ _ ℂ,
        A.val.transpose * (A.val * M) = M := by
      intro M
      calc A.val.transpose * (A.val * M)
          = (A.val.transpose * A.val) * M := by rw [Matrix.mul_assoc]
        _ = 1 * M := by rw [A.orthogonal]
        _ = M := Matrix.one_mul _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, W_transpose_eq, Winv_transpose_eq]
    simp only [Matrix.mul_assoc]
    rw [hWηW, hAorth, Winv_sq_eq_eta]
  proper := by
    rw [Matrix.det_mul, Matrix.det_mul, A.proper, mul_one,
      ← Matrix.det_mul, W_mul_Winv, Matrix.det_one]

/-- `fromSOComplex` is a left inverse of `toSOComplex`. -/
theorem fromSOComplex_toSOComplex (Λ : ComplexLorentzGroup d) :
    fromSOComplex (toSOComplex Λ) = Λ := by
  apply ext; show W * (Winv * Λ.val * W) * Winv = Λ.val
  simp only [Matrix.mul_assoc]
  rw [W_mul_Winv, Matrix.mul_one, ← Matrix.mul_assoc, W_mul_Winv, Matrix.one_mul]

/-- `toSOComplex` is a left inverse of `fromSOComplex`. -/
theorem toSOComplex_fromSOComplex (A : SOComplex (d + 1)) :
    toSOComplex (fromSOComplex A) = A := by
  apply SOComplex.ext; show Winv * (W * A.val * Winv) * W = A.val
  simp only [Matrix.mul_assoc]
  rw [Winv_mul_W, Matrix.mul_one, ← Matrix.mul_assoc, Winv_mul_W, Matrix.one_mul]

/-- `fromSOComplex` sends the orthogonal identity to the Lorentz identity. -/
theorem fromSOComplex_one :
    fromSOComplex (SOComplex.one : SOComplex (d + 1)) = (one : ComplexLorentzGroup d) := by
  apply ext; show W * SOComplex.one.val * Winv = one.val
  simp [SOComplex.one, one, W_mul_Winv]

/-- Continuity of the inverse Wick-rotation map. -/
theorem continuous_fromSOComplex :
    Continuous (fromSOComplex : SOComplex (d + 1) → ComplexLorentzGroup d) := by
  have hind : IsInducing (ComplexLorentzGroup.val : ComplexLorentzGroup d → _) := ⟨rfl⟩
  rw [hind.continuous_iff]
  show Continuous (fun A : SOComplex (d + 1) => (W : Matrix _ _ ℂ) * A.val * Winv)
  exact (continuous_const.mul SOComplex.continuous_val).mul continuous_const

/-- Every element of SO⁺(1,d;ℂ) is joined to the identity.

    The proof uses the fact that SO⁺(1,d;ℂ) ≅ SO(d+1;ℂ) via Wick rotation,
    and SO(d+1;ℂ) is connected because every element can be written as a product
    of complex 2-plane rotations, each of which is exp of a Lie algebra element
    and hence continuously connected to the identity. -/
private theorem joined_one_all (Λ : ComplexLorentzGroup d) :
    Joined (one : ComplexLorentzGroup d) Λ := by
  -- SOComplex (d + 1) is path-connected, so toSOComplex Λ is joined to SOComplex.one
  obtain ⟨γ, _⟩ := (SOComplex.isPathConnected (d + 1)).joinedIn
    SOComplex.one (Set.mem_univ _) (toSOComplex Λ) (Set.mem_univ _)
  -- Map the path back to ComplexLorentzGroup via fromSOComplex (continuous)
  have hpath : Joined (fromSOComplex SOComplex.one) (fromSOComplex (toSOComplex Λ)) :=
    ⟨γ.map continuous_fromSOComplex⟩
  rwa [fromSOComplex_one, fromSOComplex_toSOComplex] at hpath

/-- **SO⁺(1,d;ℂ) is path-connected.**

    This is the crucial fact for the Bargmann-Hall-Wightman theorem. -/
theorem isPathConnected :
    IsPathConnected (Set.univ : Set (ComplexLorentzGroup d)) := by
  rw [← pathConnectedSpace_iff_univ]
  exact PathConnectedSpace.mk ⟨one⟩ fun x y =>
    (joined_one_all x).symm.trans (joined_one_all y)

end ComplexLorentzGroup
