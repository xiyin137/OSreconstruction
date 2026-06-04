import OSReconstruction.ComplexLieGroups.SOFrameTransitivity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeSupport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurTailNormal

/-!
# Head-gauge normal-parameter data

The remaining Witt/head-normalization theorem must not merely assert that a
Schur residual tail lies on the shifted-tail variety.  It must identify the
source-variety point with a normal-parameter invariant whose head coordinate is
the local head-gauge factor.  This file records that exact data surface and
checks the mechanical consumers: residual-tail membership and the full Schur
residual packet.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The inverse Wick scale also squares to the complex Minkowski signature. -/
theorem complexMinkowskiDotInvScale_sq
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotInvScale d μ * complexMinkowskiDotInvScale d μ =
      (MinkowskiSpace.metricSignature d μ : ℂ) := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, MinkowskiSpace.metricSignature, hμ]

theorem complexMinkowskiDotInvScale_ne_zero
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotInvScale d μ ≠ 0 := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotInvScale, hμ]

theorem complexMinkowskiDotScale_mul_invScale
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotScale d μ * complexMinkowskiDotInvScale d μ = 1 := by
  rw [mul_comm]
  exact complexMinkowskiDotInvScale_mul_scale d μ

/-- The inverse Wick-scaled coordinates of a source vector. -/
def complexMinkowskiInvDotVector
    (d : ℕ) (v : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ => complexMinkowskiDotInvScale d μ * v μ

/-- The complex Minkowski pairing is also the ordinary dot pairing after
inverse Wick scaling. -/
theorem sourceVectorMinkowskiInner_eq_dot_after_invScale
    (d : ℕ) (u v : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d u v =
      ∑ μ : Fin (d + 1),
        complexMinkowskiInvDotVector d u μ *
          complexMinkowskiInvDotVector d v μ := by
  unfold sourceVectorMinkowskiInner complexMinkowskiInvDotVector
  apply Finset.sum_congr rfl
  intro μ _
  rw [← complexMinkowskiDotInvScale_sq d μ]
  ring

/-- In inverse Wick-scaled dot coordinates, `fromSOComplex A` acts by the
ordinary matrix `A`. -/
theorem complexMinkowskiInvDotVector_complexLorentzVectorAction_fromSOComplex
    (d : ℕ) (A : SOComplex (d + 1)) (v : Fin (d + 1) → ℂ) :
    complexMinkowskiInvDotVector d
        (complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A) v) =
      A.val *ᵥ complexMinkowskiInvDotVector d v := by
  ext μ
  calc
    complexMinkowskiInvDotVector d
        (complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A) v) μ
        = complexMinkowskiDotInvScale d μ *
            ∑ ν : Fin (d + 1),
              (complexMinkowskiDotScale d μ * A.val μ ν *
                complexMinkowskiDotInvScale d ν) * v ν := by
            simp [complexMinkowskiInvDotVector, complexLorentzVectorAction,
              ComplexLorentzGroup.fromSOComplex_val_apply,
              complexMinkowskiDotScale, complexMinkowskiDotInvScale]
    _ = ∑ ν : Fin (d + 1),
          (complexMinkowskiDotInvScale d μ * complexMinkowskiDotScale d μ) *
            (A.val μ ν * (complexMinkowskiDotInvScale d ν * v ν)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ν _
            ring
    _ = ∑ ν : Fin (d + 1),
          A.val μ ν * (complexMinkowskiDotInvScale d ν * v ν) := by
            rw [complexMinkowskiDotInvScale_mul_scale]
            simp
    _ = (A.val *ᵥ complexMinkowskiInvDotVector d v) μ := by
            simp [complexMinkowskiInvDotVector, Matrix.mulVec, dotProduct]

/-- The signed dot-scale attached to the `a`th Minkowski prefix coordinate. -/
def minkowskiPrefixSigma (m r : ℕ) (a : Fin r) : ℂ :=
  complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a)

theorem minkowskiPrefixSigma_ne_zero
    (m r : ℕ) (a : Fin r) :
    minkowskiPrefixSigma m r a ≠ 0 :=
  complexMinkowskiDotInvScale_ne_zero (m + r) (SOComplex.prefixCol m r a)

theorem minkowskiPrefixSigma_sq
    (m r : ℕ) (a : Fin r) :
    minkowskiPrefixSigma m r a ^ 2 =
      (MinkowskiSpace.metricSignature (m + r)
        (SOComplex.prefixCol m r a) : ℂ) := by
  simp [minkowskiPrefixSigma, sq, complexMinkowskiDotInvScale_sq]

/-- Determinant-one complex Lorentz transitivity for a source frame whose Gram
matrix is the standard Minkowski prefix metric. -/
def complexMinkowski_detOneWittExtension_to_canonicalPrefixFrame
    (m r : ℕ)
    (x : Fin r → Fin (m + r + 1) → ℂ)
    (hgram :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner (m + r) (x a) (x b) =
          if a = b then
            (MinkowskiSpace.metricSignature (m + r)
              (SOComplex.prefixCol m r a) : ℂ)
          else 0) :
    { Λ : ComplexLorentzGroup (m + r) //
      ∀ a : Fin r,
        complexLorentzVectorAction Λ (x a) =
          fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0 } := by
  let σ : Fin r → ℂ := minkowskiPrefixSigma m r
  let xdot : Fin r → Fin (m + r + 1) → ℂ :=
    fun a => complexMinkowskiInvDotVector (m + r) (x a)
  have hσ : ∀ a : Fin r, σ a ≠ 0 := by
    intro a
    exact minkowskiPrefixSigma_ne_zero m r a
  have hdotGram :
      ∀ a b : Fin r,
        (∑ k : Fin (m + r + 1), xdot a k * xdot b k) =
          if a = b then (σ a) ^ 2 else 0 := by
    intro a b
    rw [← sourceVectorMinkowskiInner_eq_dot_after_invScale (m + r) (x a) (x b)]
    rw [hgram a b]
    by_cases hab : a = b
    · subst hab
      simp [σ, minkowskiPrefixSigma_sq]
    · simp [hab]
  let A : SOComplex (m + r + 1) :=
    Classical.choose
      (SOComplex.exists_so_with_signedPrefixCols m r σ hσ xdot hdotGram)
  have hA :
      ∀ (a : Fin r) (k : Fin (m + r + 1)),
        σ a * A.val k (SOComplex.prefixCol m r a) = xdot a k :=
    Classical.choose_spec
      (SOComplex.exists_so_with_signedPrefixCols m r σ hσ xdot hdotGram)
  refine ⟨ComplexLorentzGroup.fromSOComplex A⁻¹, ?_⟩
  intro a
  have hAinv_xdot :
      (A⁻¹).val *ᵥ xdot a =
        fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := by
    ext μ
    have horth := congrFun (congrFun A.orthogonal μ) (SOComplex.prefixCol m r a)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at horth
    calc
      ((A⁻¹).val *ᵥ xdot a) μ
          = ∑ k : Fin (m + r + 1), A.val k μ * xdot a k := by
              simp [Matrix.mulVec, dotProduct, SOComplex.inv_val_apply]
      _ = ∑ k : Fin (m + r + 1),
            A.val k μ * (σ a * A.val k (SOComplex.prefixCol m r a)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hA a k]
      _ = σ a *
            ∑ k : Fin (m + r + 1),
              A.val k μ * A.val k (SOComplex.prefixCol m r a) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = σ a * (if μ = SOComplex.prefixCol m r a then 1 else 0) := by
              rw [horth]
      _ = (if μ = SOComplex.prefixCol m r a then σ a else 0) := by
              by_cases hμ : μ = SOComplex.prefixCol m r a <;> simp [hμ]
  have hdot_action :
      complexMinkowskiInvDotVector (m + r)
          (complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)) =
        fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := by
    calc
      complexMinkowskiInvDotVector (m + r)
          (complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a))
          = (A⁻¹).val *ᵥ xdot a := by
              rw [complexMinkowskiInvDotVector_complexLorentzVectorAction_fromSOComplex]
      _ = fun μ => if μ = SOComplex.prefixCol m r a then σ a else 0 := hAinv_xdot
  ext μ
  by_cases hμ : μ = SOComplex.prefixCol m r a
  · subst hμ
    have hμdot :
        complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a) *
          complexLorentzVectorAction
            (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
            (SOComplex.prefixCol m r a) =
          σ a := by
      simpa [complexMinkowskiInvDotVector] using
        congrFun hdot_action (SOComplex.prefixCol m r a)
    calc
      complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
          (SOComplex.prefixCol m r a)
          = 1 *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a) := by rw [one_mul]
      _ = (complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a)) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a) := by
            rw [complexMinkowskiDotScale_mul_invScale]
      _ = complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            (complexMinkowskiDotInvScale (m + r) (SOComplex.prefixCol m r a) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a)
                (SOComplex.prefixCol m r a)) := by ring
      _ = complexMinkowskiDotScale (m + r) (SOComplex.prefixCol m r a) *
            σ a := by
            rw [hμdot]
      _ = 1 := by
            simp [σ, minkowskiPrefixSigma, complexMinkowskiDotScale_mul_invScale]
      _ = (fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0)
            (SOComplex.prefixCol m r a) := by
            simp
  · calc
      complexLorentzVectorAction (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ
          = 1 *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ := by
            rw [one_mul]
      _ = (complexMinkowskiDotScale (m + r) μ *
            complexMinkowskiDotInvScale (m + r) μ) *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ := by
            rw [complexMinkowskiDotScale_mul_invScale]
      _ = complexMinkowskiDotScale (m + r) μ *
            (complexMinkowskiDotInvScale (m + r) μ *
              complexLorentzVectorAction
                (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ) := by ring
      _ = 0 := by
            rw [show
              complexMinkowskiDotInvScale (m + r) μ *
                complexLorentzVectorAction
                  (ComplexLorentzGroup.fromSOComplex A⁻¹) (x a) μ =
                0 by
                  simpa [complexMinkowskiInvDotVector, hμ] using
                    congrFun hdot_action μ]
            ring
      _ = (fun μ => if μ = SOComplex.prefixCol m r a then 1 else 0) μ := by
            simp [hμ]

/-- Reindexing the ambient `Fin (d+1)` coordinates along an equality of
spacetime dimensions preserves the source Minkowski pairing. -/
theorem sourceVectorMinkowskiInner_cast_eq
    {D E : ℕ} (h : D = E)
    (u v : Fin (E + 1) → ℂ) :
    sourceVectorMinkowskiInner D
        (fun μ : Fin (D + 1) => u (Fin.cast (by omega : D + 1 = E + 1) μ))
        (fun μ : Fin (D + 1) => v (Fin.cast (by omega : D + 1 = E + 1) μ)) =
      sourceVectorMinkowskiInner E u v := by
  subst E
  simp

/-- The Minkowski signature is invariant under the same ambient `Fin` cast. -/
theorem minkowskiMetricSignature_cast_eq
    {D E : ℕ} (h : D = E) (μ : Fin (D + 1)) :
    MinkowskiSpace.metricSignature D μ =
      MinkowskiSpace.metricSignature E
        (Fin.cast (by omega : D + 1 = E + 1) μ) := by
  subst E
  simp

/-- Reindexing a Lorentz transformation along an equality of spacetime
dimensions commutes with the pointwise vector action. -/
theorem complexLorentzVectorAction_cast_eq
    {D E : ℕ} (h : D = E)
    (Λ : ComplexLorentzGroup D) (v : Fin (E + 1) → ℂ) :
    complexLorentzVectorAction (h ▸ Λ) v =
      fun μ : Fin (E + 1) =>
        complexLorentzVectorAction Λ
          (fun ν : Fin (D + 1) =>
            v (Fin.cast (by omega : D + 1 = E + 1) ν))
          (Fin.cast (by omega : E + 1 = D + 1) μ) := by
  subst E
  simp

/-- Determinant-one complex Lorentz transitivity for the canonical selected
head coordinates `0, ..., r-1` inside `Fin (d+1)`. -/
def complexMinkowski_detOneWittExtension_to_canonicalHeadFrame
    (d r : ℕ)
    (hrD : r < d + 1)
    (x : Fin r → Fin (d + 1) → ℂ)
    (hgram :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner d (x a) (x b) =
          if a = b then
            (MinkowskiSpace.metricSignature d
              (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
          else 0) :
    { Λ : ComplexLorentzGroup d //
      ∀ a : Fin r,
        complexLorentzVectorAction Λ (x a) =
          fun μ => if μ = finSourceHead (Nat.le_of_lt hrD) a then 1 else 0 } := by
  let D := (d - r) + r
  let hD : D = d := by omega
  let hN : D + 1 = d + 1 := by omega
  let x' : Fin r → Fin (D + 1) → ℂ :=
    fun a μ => x a (Fin.cast hN μ)
  have hgram' :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner D (x' a) (x' b) =
          if a = b then
            (MinkowskiSpace.metricSignature D
              (SOComplex.prefixCol (d - r) r a) : ℂ)
          else 0 := by
    intro a b
    calc
      sourceVectorMinkowskiInner D (x' a) (x' b)
          = sourceVectorMinkowskiInner d (x a) (x b) := by
              simpa [D, x', hN] using
                sourceVectorMinkowskiInner_cast_eq hD (x a) (x b)
      _ = if a = b then
            (MinkowskiSpace.metricSignature d
              (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
          else 0 := hgram a b
      _ = if a = b then
            (MinkowskiSpace.metricSignature D
              (SOComplex.prefixCol (d - r) r a) : ℂ)
          else 0 := by
          by_cases hab : a = b
          · subst b
            have hprefix :
                Fin.cast hN (SOComplex.prefixCol (d - r) r a) =
                  finSourceHead (Nat.le_of_lt hrD) a := by
              ext
              simp [D, SOComplex.prefixCol, finSourceHead]
            simp
            rw [← hprefix]
            exact_mod_cast
              (minkowskiMetricSignature_cast_eq hD
                (SOComplex.prefixCol (d - r) r a)).symm
          · simp [hab]
  obtain ⟨Λ0, hΛ0⟩ :=
    complexMinkowski_detOneWittExtension_to_canonicalPrefixFrame
      (d - r) r x' hgram'
  refine ⟨hD ▸ Λ0, ?_⟩
  intro a
  ext μ
  have hact := congrFun (hΛ0 a) (Fin.cast (by omega : d + 1 = D + 1) μ)
  have hcast_eq :
      Fin.cast (by omega : d + 1 = D + 1) μ =
        SOComplex.prefixCol (d - r) r a ↔
      μ = finSourceHead (Nat.le_of_lt hrD) a := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [D, SOComplex.prefixCol, finSourceHead] using hv
    · intro h
      subst μ
      ext
      simp [D, SOComplex.prefixCol, finSourceHead]
  calc
    complexLorentzVectorAction (hD ▸ Λ0) (x a) μ
        = complexLorentzVectorAction Λ0 (x' a)
            (Fin.cast (by omega : d + 1 = D + 1) μ) := by
            simpa [x', D, hN] using
              congrFun (complexLorentzVectorAction_cast_eq hD Λ0 (x a)) μ
    _ = (fun μ : Fin (D + 1) =>
          if μ = SOComplex.prefixCol (d - r) r a then 1 else 0)
          (Fin.cast (by omega : d + 1 = D + 1) μ) := hact
    _ = (fun μ => if μ = finSourceHead (Nat.le_of_lt hrD) a then 1 else 0)
          μ := by
          change (if Fin.cast (by omega : d + 1 = D + 1) μ =
              SOComplex.prefixCol (d - r) r a then 1 else 0) =
            (if μ = finSourceHead (Nat.le_of_lt hrD) a then 1 else 0)
          by_cases hμ : μ = finSourceHead (Nat.le_of_lt hrD) a
          · rw [if_pos (hcast_eq.mpr hμ), if_pos hμ]
          · have hc :
                Fin.cast (by omega : d + 1 = D + 1) μ ≠
                  SOComplex.prefixCol (d - r) r a := by
              intro hc
              exact hμ (hcast_eq.mp hc)
            rw [if_neg hc, if_neg hμ]

/-- The Lorentz vector action distributes over finite complex linear
combinations. -/
theorem complexLorentzVectorAction_linearCombination
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Λ : ComplexLorentzGroup d) (c : ι → ℂ)
    (v : ι → Fin (d + 1) → ℂ) :
    complexLorentzVectorAction Λ (fun μ => ∑ i, c i * v i μ) =
      fun μ => ∑ i, c i * complexLorentzVectorAction Λ (v i) μ := by
  calc
    complexLorentzVectorAction Λ (fun μ => ∑ i, c i * v i μ)
        = fun μ => ∑ i,
            complexLorentzVectorAction Λ (fun μ => c i * v i μ) μ := by
            simpa using
              complexLorentzVectorAction_sum Λ (fun i μ => c i * v i μ)
    _ = fun μ => ∑ i, c i * complexLorentzVectorAction Λ (v i) μ := by
            ext μ
            apply Finset.sum_congr rfl
            intro i _
            exact congrFun (complexLorentzVectorAction_smul Λ (c i) (v i)) μ

/-- Determinant-one complex Lorentz transitivity from a selected head frame to
the head-gauge factor frame. -/
def complexMinkowski_detOneWittExtension_to_headFactorFrame
    [NeZero d]
    (_hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (hHdet : IsUnit H.det)
    (x y : Fin r → Fin (d + 1) → ℂ)
    (_hx : LinearIndependent ℂ x)
    (hy :
      y =
        fun a =>
          sourceOrientedNormalHeadVector d n r hrD hrn
            { head := H, mixed := 0, tail := 0 } a)
    (hxGram :
      ∀ a b,
        sourceVectorMinkowskiInner d (x a) (x b) =
          (H * sourceHeadMetric d r hrD * H.transpose) a b) :
    { Λ : ComplexLorentzGroup d //
      ∀ a, complexLorentzVectorAction Λ (x a) = y a } := by
  let Hinv := H⁻¹
  let x0 : Fin r → Fin (d + 1) → ℂ :=
    fun a μ => ∑ b : Fin r, Hinv a b * x b μ
  have hgram0 :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner d (x0 a) (x0 b) =
          if a = b then
            (MinkowskiSpace.metricSignature d
              (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
          else 0 := by
    intro a b
    let Gram := H * sourceHeadMetric d r hrD * Hᵀ
    have hraw :
        sourceVectorMinkowskiInner d (x0 a) (x0 b) =
          sourceHeadMetric d r hrD a b := by
      calc
        sourceVectorMinkowskiInner d (x0 a) (x0 b)
            = ∑ i : Fin r, H⁻¹ a i *
                ∑ j : Fin r, H⁻¹ b j *
                  sourceVectorMinkowskiInner d (x i) (x j) := by
                change sourceVectorMinkowskiInner d
                  (fun μ => ∑ i : Fin r, H⁻¹ a i * x i μ)
                  (fun μ => ∑ j : Fin r, H⁻¹ b j * x j μ) = _
                rw [sourceVectorMinkowskiInner_sum_left]
                simp_rw [sourceVectorMinkowskiInner_smul_left]
                simp_rw [sourceVectorMinkowskiInner_sum_right]
                simp_rw [sourceVectorMinkowskiInner_smul_right]
        _ = ∑ i : Fin r, H⁻¹ a i *
                ∑ j : Fin r, H⁻¹ b j * Gram i j := by
                apply Finset.sum_congr rfl
                intro i _
                congr 1
                apply Finset.sum_congr rfl
                intro j _
                rw [hxGram]
        _ = ∑ j : Fin r, H⁻¹ b j * ∑ i : Fin r, H⁻¹ a i * Gram i j := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j _
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ((H⁻¹ * Gram * (H⁻¹)ᵀ) a b) := by
                simp [Matrix.mul_apply, Matrix.transpose_apply,
                  mul_comm]
        _ = sourceHeadMetric d r hrD a b := by
                calc
                  (H⁻¹ * Gram * (H⁻¹)ᵀ) a b =
                      ((H⁻¹ * H) * sourceHeadMetric d r hrD *
                        (Hᵀ * (H⁻¹)ᵀ)) a b := by
                      simp [Gram, Matrix.mul_assoc]
                  _ = ((1 : Matrix (Fin r) (Fin r) ℂ) *
                        sourceHeadMetric d r hrD *
                        (1 : Matrix (Fin r) (Fin r) ℂ)) a b := by
                      rw [Matrix.nonsing_inv_mul H hHdet]
                      have ht :
                          Hᵀ * (H⁻¹)ᵀ =
                            (1 : Matrix (Fin r) (Fin r) ℂ) := by
                        rw [← Matrix.transpose_mul,
                          Matrix.nonsing_inv_mul H hHdet]
                        simp
                      rw [ht]
                  _ = sourceHeadMetric d r hrD a b := by simp
    simpa [sourceHeadMetric_apply] using hraw
  obtain ⟨Λ, hΛ0⟩ :=
    complexMinkowski_detOneWittExtension_to_canonicalHeadFrame
      d r hrD x0 hgram0
  refine ⟨Λ, ?_⟩
  intro a
  have hx_decomp :
      x a = fun μ => ∑ b : Fin r, H a b * x0 b μ := by
    ext μ
    calc
      x a μ =
          ((1 : Matrix (Fin r) (Fin r) ℂ) *ᵥ
            (fun c : Fin r => x c μ)) a := by
            simp
      _ = ((H * H⁻¹) *ᵥ (fun c : Fin r => x c μ)) a := by
            rw [Matrix.mul_nonsing_inv H hHdet]
      _ = (H *ᵥ (H⁻¹ *ᵥ (fun c : Fin r => x c μ))) a := by
            rw [Matrix.mulVec_mulVec]
      _ = ∑ b : Fin r, H a b * x0 b μ := by
            simp [x0, Hinv, Matrix.mulVec, dotProduct]
  calc
    complexLorentzVectorAction Λ (x a)
        = complexLorentzVectorAction Λ
            (fun μ => ∑ b : Fin r, H a b * x0 b μ) := by
            rw [hx_decomp]
    _ = fun μ => ∑ b : Fin r,
          H a b * complexLorentzVectorAction Λ (x0 b) μ := by
            exact
              complexLorentzVectorAction_linearCombination
                Λ (fun b => H a b) x0
    _ = fun μ => ∑ b : Fin r, H a b *
          (if μ = finSourceHead (Nat.le_of_lt hrD) b then 1 else 0) := by
            ext μ
            apply Finset.sum_congr rfl
            intro b _
            rw [congrFun (hΛ0 b) μ]
    _ = y a := by
            rw [hy]
            ext μ
            change
              (∑ b : Fin r, H a b *
                (if μ = finSourceHead (Nat.le_of_lt hrD) b then 1 else 0)) =
              ∑ b : Fin r, H a b *
                hwLemma3CanonicalSource d n r (finSourceHead hrn b) μ
            apply Finset.sum_congr rfl
            intro b _
            rw [hwLemma3CanonicalSource_head_apply d n r hrD hrn b μ]

/-- Normal-parameter representative data matched to a local head gauge.

The hard geometric producer for this structure is the finite-dimensional
proper-complex Witt extension carrying the actual selected head frame to the
head-gauge frame, followed by the Schur decomposition of the remaining tail
vectors. -/
structure SourceOrientedHeadGaugeNormalParameterData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD) where
  p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn
  invariant_eq :
    G =
      sourceOrientedMinkowskiInvariant d n
        (sourceOrientedNormalParameterVector d n r hrD hrn p)
  head_eq :
    Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
      p.head

/-- The normal parameter whose head coordinate is the local head-gauge factor
and whose mixed/tail coordinates are zero.  This is the target head frame used
before the transformed tail coordinates are chosen. -/
def sourceOrientedHeadGaugeHeadParameter
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD) :
    SourceOrientedRankDeficientNormalParameter d n r hrD hrn where
  head := Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  mixed := 0
  tail := 0

@[simp]
theorem sourceOrientedHeadGaugeHeadParameter_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD) :
    (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head).head =
      Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) := by
  rfl

/-- The local head gauge identifies the actual selected head Gram matrix with
the normal-form head Gram matrix of the gauge head frame. -/
theorem sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (a b : Fin r) :
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
      sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
        (sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) b) := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hfactor :
      p0.head * sourceHeadMetric d r hrD * p0.headᵀ =
        sourceOrientedSchurHeadBlock n r hrn G := by
    simpa [Acoord, p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_gram Acoord hHead
  calc
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (z (finSourceHead hrn b)) =
        sourceOrientedSchurHeadBlock n r hrn G a b := by
          subst G
          rfl
    _ = (p0.head * sourceHeadMetric d r hrD * p0.headᵀ) a b := by
          rw [hfactor]
    _ = sourceVectorMinkowskiInner d
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 a)
        (sourceOrientedNormalHeadVector d n r hrD hrn p0 b) := by
          exact
            (sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector
              d n r hrD hrn p0 a b).symm

/-- The gauge normal head frame is linearly independent. -/
theorem sourceOriented_headGauge_normalHead_linearIndependent
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    LinearIndependent ℂ
      (fun a : Fin r =>
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) := by
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  have hp0_det : IsUnit p0.head.det := by
    simpa [p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_det_unit
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hη : IsUnit (sourceHeadMetric d r hrD).det :=
    sourceHeadMetric_det_isUnit d r hrD
  have hp0t : IsUnit p0.headᵀ.det :=
    Matrix.isUnit_det_transpose p0.head hp0_det
  have hheadGram :
      IsUnit (p0.head * sourceHeadMetric d r hrD * p0.headᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hp0_det.mul hη).mul hp0t
  have hA :
      IsUnit
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p0))).det := by
    rw [sourceOrientedSchurHeadBlock_normalParameter]
    exact hheadGram
  have hLI :=
    sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
      d n r hrn
      (sourceOrientedNormalParameterVector d n r hrD hrn p0) hA
  simpa [sourceOrientedNormalParameterVector_head] using hLI

/-- Checked same-Gram frame data supplied by a local head gauge.

The hard Witt theorem should consume precisely this finite-dimensional packet:
the actual selected head frame and the gauge normal head frame are linearly
independent and have the same nondegenerate Gram matrix. -/
structure SourceOrientedHeadGaugeFrameSameGramData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) where
  actual_linearIndependent :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a))
  normal_linearIndependent :
    LinearIndependent ℂ
      (fun a : Fin r =>
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
  same_gram :
    ∀ a b : Fin r,
      sourceVectorMinkowskiInner d
          (z (finSourceHead hrn a))
          (z (finSourceHead hrn b)) =
        sourceVectorMinkowskiInner d
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a)
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) b)
  headGram_det_unit :
    IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det

/-- A local head gauge mechanically produces the same-Gram frame packet needed
by the remaining determinant-one Witt step. -/
def sourceOriented_headGaugeFrameSameGramData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    SourceOrientedHeadGaugeFrameSameGramData
      d n r hrD hrn Head hGvar hHead hz where
  actual_linearIndependent :=
    sourceHeadRows_linearIndependent_of_headFactor
      d n r hrD hrn hGvar Head hHead hz
  normal_linearIndependent :=
    sourceOriented_headGauge_normalHead_linearIndependent
      d n r hrD hrn hGvar Head hHead
  same_gram :=
    sourceOriented_headGauge_actualHeadGram_eq_normalHeadGram
      d n r hrD hrn hGvar Head hHead hz
  headGram_det_unit :=
    sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
      d n r hrD hrn hGvar Head hHead

/-- Pairing a vector against a canonical head coordinate vector extracts the
corresponding diagonal-sign-weighted head coordinate. -/
theorem sourceVectorMinkowskiInner_right_hwLemma3CanonicalSource_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (v : Fin (d + 1) → ℂ)
    (a : Fin r) :
    sourceVectorMinkowskiInner d v
        (hwLemma3CanonicalSource d n r (finSourceHead hrn a)) =
      (MinkowskiSpace.metricSignature d
          (finSourceHead (Nat.le_of_lt hrD) a) : ℂ) *
        v (finSourceHead (Nat.le_of_lt hrD) a) := by
  rw [sourceVectorMinkowskiInner]
  rw [Finset.sum_eq_single (finSourceHead (Nat.le_of_lt hrD) a)]
  · rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
    simp
  · intro μ _hμ hne
    have hzero :
        hwLemma3CanonicalSource d n r (finSourceHead hrn a) μ = 0 := by
      rw [hwLemma3CanonicalSource_head_apply (hrD := hrD)]
      simp [hne]
    simp [hzero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- A vector orthogonal to every gauge normal head vector has zero canonical
head coordinates. -/
theorem sourceOriented_headGauge_headCoord_eq_zero_of_orthogonal_normalHead
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {v : Fin (d + 1) → ℂ}
    (horth :
      ∀ a : Fin r,
        sourceVectorMinkowskiInner d v
          (sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) =
          0)
    (a : Fin r) :
    v (finSourceHead (Nat.le_of_lt hrD) a) = 0 := by
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  let H := p0.head
  let u : Fin r → ℂ := fun b =>
    (MinkowskiSpace.metricSignature d
      (finSourceHead (Nat.le_of_lt hrD) b) : ℂ) *
      v (finSourceHead (Nat.le_of_lt hrD) b)
  have hHdet : IsUnit H.det := by
    simpa [H, p0, sourceOrientedHeadGaugeHeadParameter] using
      Head.factor_det_unit
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hHu : H.mulVec u = 0 := by
    ext b
    have hpair :
        sourceVectorMinkowskiInner d v
          (sourceOrientedNormalHeadVector d n r hrD hrn p0 b) =
        H.mulVec u b := by
      change
        sourceVectorMinkowskiInner d v
          (fun μ =>
            ∑ c : Fin r,
              p0.head b c *
                hwLemma3CanonicalSource d n r (finSourceHead hrn c) μ) =
          H.mulVec u b
      rw [sourceVectorMinkowskiInner_sum_right]
      simp_rw [sourceVectorMinkowskiInner_smul_right]
      simp_rw [
        sourceVectorMinkowskiInner_right_hwLemma3CanonicalSource_head
          d n r hrD hrn v]
      simp [H, u, Matrix.mulVec, dotProduct]
    exact hpair.symm.trans (horth b)
  have hu : u = 0 := by
    have hleft :
        H⁻¹.mulVec (H.mulVec u) = H⁻¹.mulVec (0 : Fin r → ℂ) := by
      rw [hHu]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hHdet,
      Matrix.one_mulVec] at hleft
    simpa using hleft
  have ha := congrFun hu a
  have hmetric_ne :
      (MinkowskiSpace.metricSignature d
        (finSourceHead (Nat.le_of_lt hrD) a) : ℂ) ≠ 0 := by
    by_cases h0 : finSourceHead (Nat.le_of_lt hrD) a = 0
    · simp [MinkowskiSpace.metricSignature, h0]
    · simp [MinkowskiSpace.metricSignature, h0]
  exact (mul_eq_zero.mp ha).resolve_left hmetric_ne

/-- A spacetime vector with zero canonical head coordinates is exactly the
tail embedding of its canonical tail coordinates. -/
theorem eq_sourceTailEmbed_of_headCoord_eq_zero
    (d r : ℕ)
    (hrD : r < d + 1)
    (v : Fin (d + 1) → ℂ)
    (hhead : ∀ a : Fin r, v (finSourceHead (Nat.le_of_lt hrD) a) = 0) :
    v =
      sourceTailEmbed d r hrD
        (fun u : Fin (d + 1 - r) =>
          v (finSourceTail (Nat.le_of_lt hrD) u)) := by
  ext μ
  rcases finSourceHead_tail_cases (Nat.le_of_lt hrD) μ with
    ⟨a, rfl⟩ | ⟨u, rfl⟩
  · simp [sourceTailEmbed, hhead a]
  · simp [sourceTailEmbed]

/-- Constructive tail-coordinate data after a Lorentz transformation has
normalized the selected head frame to the gauge normal head frame. -/
def sourceOriented_headGaugeTailCoordinatesAfterWittData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    { q : Fin (n - r) → Fin (d + 1 - r) → ℂ //
      let H :=
        Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
      let L :=
        sourceSchurMixedCoeff n r hrn G
          (sourceOrientedSchurHeadBlock n r hrn G)
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn
          { head := H
            mixed := L
            tail := q } } := by
  let A := sourceOrientedSchurHeadBlock n r hrn G
  let H := Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  let L := sourceSchurMixedCoeff n r hrn G A
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  let y : Fin r → Fin (d + 1) → ℂ := fun a =>
    sourceOrientedNormalHeadVector d n r hrD hrn p0 a
  let w := complexLorentzAction Λ z
  let res : Fin (n - r) → Fin (d + 1) → ℂ := fun u μ =>
    w (finSourceTail hrn u) μ - ∑ a : Fin r, L u a * y a μ
  let q : Fin (n - r) → Fin (d + 1 - r) → ℂ := fun u β =>
    res u (finSourceTail (Nat.le_of_lt hrD) β)
  refine ⟨q, ?_⟩
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := H
      mixed := L
      tail := q }
  change w = sourceOrientedNormalParameterVector d n r hrD hrn p
  have hAunit : IsUnit A.det := by
    simpa [A] using
      sourceOrientedSchurHeadBlock_det_isUnit_of_headFactor
        d n r hrD hrn hGvar Head hHead
  have hLmul :
      L * A = sourceOrientedSchurMixedBlock n r hrn G := by
    simpa [L, A] using
      sourceSchurMixedCoeff_mul_headBlock n r hrn G A hAunit
  have hfactor : H * sourceHeadMetric d r hrD * Hᵀ = A := by
    simpa [H, A] using
      Head.factor_gram
        (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead
  have hygram :
      ∀ a b : Fin r, sourceVectorMinkowskiInner d (y a) (y b) = A a b := by
    intro a b
    calc
      sourceVectorMinkowskiInner d (y a) (y b) =
          (p0.head * sourceHeadMetric d r hrD * p0.headᵀ) a b := by
            simp [y, p0,
              sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
      _ = A a b := by
            simpa [p0, sourceOrientedHeadGaugeHeadParameter, H] using
              congrFun (congrFun hfactor a) b
  have hgramW : sourceMinkowskiGram d n w = G.gram := by
    calc
      sourceMinkowskiGram d n w =
          sourceMinkowskiGram d n z := by
            exact sourceMinkowskiGram_complexLorentzAction
              (d := d) (n := n) Λ z
      _ = G.gram := by
            rw [hz]
            rfl
  have htail_head :
      ∀ u a,
        sourceVectorMinkowskiInner d (w (finSourceTail hrn u)) (y a) =
          sourceOrientedSchurMixedBlock n r hrn G u a := by
    intro u a
    calc
      sourceVectorMinkowskiInner d (w (finSourceTail hrn u)) (y a) =
          sourceVectorMinkowskiInner d
            (w (finSourceTail hrn u)) (w (finSourceHead hrn a)) := by
            have hyw : y a = w (finSourceHead hrn a) :=
              (hΛhead a).symm
            rw [hyw]
      _ = sourceMinkowskiGram d n w (finSourceTail hrn u)
            (finSourceHead hrn a) := rfl
      _ = G.gram (finSourceTail hrn u) (finSourceHead hrn a) := by
            rw [hgramW]
      _ = sourceOrientedSchurMixedBlock n r hrn G u a := rfl
  have hres_orth :
      ∀ u a, sourceVectorMinkowskiInner d (res u) (y a) = 0 := by
    intro u a
    calc
      sourceVectorMinkowskiInner d (res u) (y a) =
          sourceOrientedSchurMixedBlock n r hrn G u a -
            (L * A) u a := by
            simp [res, sourceVectorMinkowskiInner_sub_left,
              sourceVectorMinkowskiInner_sum_left,
              sourceVectorMinkowskiInner_smul_left, htail_head, hygram,
              Matrix.mul_apply]
      _ = 0 := by
            rw [hLmul]
            simp
  have hres_tail :
      ∀ u, res u = sourceTailEmbed d r hrD (q u) := by
    intro u
    apply eq_sourceTailEmbed_of_headCoord_eq_zero d r hrD
    intro a
    exact
      sourceOriented_headGauge_headCoord_eq_zero_of_orthogonal_normalHead
        d n r hrD hrn hGvar Head hHead (hres_orth u) a
  ext i μ
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · calc
      w (finSourceHead hrn a) μ = y a μ := congrFun (hΛhead a) μ
      _ = sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceHead hrn a) μ := by
            simp [p, y, p0, sourceOrientedNormalParameterVector_head,
              sourceOrientedHeadGaugeHeadParameter, H, sourceOrientedNormalHeadVector]
  · have htail :
        w (finSourceTail hrn u) =
          (fun μ =>
            (∑ a : Fin r,
              L u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
              sourceTailEmbed d r hrD (q u) μ) := by
      ext ν
      have hresν := congrFun (hres_tail u) ν
      rw [sub_eq_iff_eq_add] at hresν
      simpa [res, q, y, p, p0, sourceOrientedHeadGaugeHeadParameter, H,
        sourceOrientedNormalHeadVector, add_comm, add_left_comm, add_assoc]
        using hresν
    calc
      w (finSourceTail hrn u) μ =
          ((fun μ =>
            (∑ a : Fin r,
              L u a *
                sourceOrientedNormalHeadVector d n r hrD hrn p a μ) +
              sourceTailEmbed d r hrD (q u) μ) μ) := congrFun htail μ
      _ = sourceOrientedNormalParameterVector d n r hrD hrn p
          (finSourceTail hrn u) μ := by
            rw [sourceOrientedNormalParameterVector_tail]

/-- After a Lorentz transformation has normalized the selected head frame to
the gauge normal head frame, the transformed tail labels have the corresponding
Schur mixed coordinates plus canonical shifted-tail coordinates. -/
theorem sourceOriented_headGauge_tailCoordinates_after_witt
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    ∃ q : Fin (n - r) → Fin (d + 1 - r) → ℂ,
      let H :=
        Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
      let L :=
        sourceSchurMixedCoeff n r hrn G
          (sourceOrientedSchurHeadBlock n r hrn G)
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn
          { head := H
            mixed := L
            tail := q } := by
  let Q :=
    sourceOriented_headGaugeTailCoordinatesAfterWittData
      d n r hrD hrn Head hGvar hHead hz Λ hΛhead
  exact ⟨Q.1, Q.2⟩

/-- Once the determinant-one Witt step supplies a Lorentz transformation
normalizing the selected head frame, the matched head-gauge normal-parameter
data is fully mechanical. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_head_normalized
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalHeadVector d n r hrD hrn
            (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head := by
  let Q :=
    sourceOriented_headGaugeTailCoordinatesAfterWittData
      d n r hrD hrn Head hGvar hHead hz Λ hΛhead
  let q := Q.1
  let H :=
    Head.factor (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)
  let L :=
    sourceSchurMixedCoeff n r hrn G
      (sourceOrientedSchurHeadBlock n r hrn G)
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := H
      mixed := L
      tail := q }
  have hq :
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn p := by
    simpa [q, H, L, p] using Q.2
  exact
    { p := p
      invariant_eq := by
        calc
          G = sourceOrientedMinkowskiInvariant d n z := hz
          _ = sourceOrientedMinkowskiInvariant d n
                (complexLorentzAction Λ z) := by
              exact (sourceOrientedMinkowskiInvariant_complexLorentzAction
                (d := d) (n := n) Λ z).symm
          _ = sourceOrientedMinkowskiInvariant d n
                (sourceOrientedNormalParameterVector d n r hrD hrn p) := by
              rw [hq]
      head_eq := by
        rfl }

/-- Typed output of the remaining determinant-one Witt head-normalization
theorem.

This is deliberately a `Type`-valued structure rather than a bare existential:
the downstream normal-parameter data contains computed tail coordinates, so
Lean must be able to use the chosen Lorentz element constructively. -/
structure SourceOrientedHeadGaugeWittData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) where
  Λ : ComplexLorentzGroup d
  head_normalized :
    ∀ a : Fin r,
      complexLorentzAction Λ z (finSourceHead hrn a) =
        sourceOrientedNormalHeadVector d n r hrD hrn
          (sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head) a

namespace SourceOrientedHeadGaugeWittData

/-- The checked consumer from typed Witt head-normalization data to matched
normal-parameter data. -/
def normalParameterData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    (W : SourceOrientedHeadGaugeWittData
      d n r hrD hrn Head hGvar hHead hz) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  sourceOriented_headGaugeNormalParameterData_of_lorentz_head_normalized
    d n r hrD hrn Head hGvar hHead hz W.Λ W.head_normalized

end SourceOrientedHeadGaugeWittData

/-- The local head gauge supplies the finite-dimensional Witt data normalizing
the selected actual head frame to the gauge normal head frame. -/
def sourceOriented_headGaugeWittData
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    SourceOrientedHeadGaugeWittData
      d n r hrD hrn Head hGvar hHead hz := by
  let Acoord := sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar
  let H := Head.factor Acoord
  let p0 := sourceOrientedHeadGaugeHeadParameter d n r hrD hrn hGvar Head
  let x : Fin r → Fin (d + 1) → ℂ := fun a => z (finSourceHead hrn a)
  let y : Fin r → Fin (d + 1) → ℂ := fun a =>
    sourceOrientedNormalHeadVector d n r hrD hrn p0 a
  let F :=
    sourceOriented_headGaugeFrameSameGramData
      d n r hrD hrn Head hGvar hHead hz
  have hHdet : IsUnit H.det := by
    simpa [H, Acoord] using Head.factor_det_unit Acoord hHead
  have hy :
      y =
        fun a =>
          sourceOrientedNormalHeadVector d n r hrD hrn
            { head := H, mixed := 0, tail := 0 } a := by
    rfl
  have hxGram :
      ∀ a b,
        sourceVectorMinkowskiInner d (x a) (x b) =
          (H * sourceHeadMetric d r hrD * H.transpose) a b := by
    intro a b
    calc
      sourceVectorMinkowskiInner d (x a) (x b) =
          sourceVectorMinkowskiInner d (y a) (y b) := by
            exact F.same_gram a b
      _ = (H * sourceHeadMetric d r hrD * H.transpose) a b := by
            simpa [x, y, p0, H, Acoord,
              sourceOrientedHeadGaugeHeadParameter] using
              sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector
                d n r hrD hrn p0 a b
  let W :=
    complexMinkowski_detOneWittExtension_to_headFactorFrame
      hd hrD hrn H hHdet x y F.actual_linearIndependent hy hxGram
  exact
    { Λ := W.1
      head_normalized := by
        intro a
        simpa [x, y, complexLorentzAction] using W.2 a }

/-- Full matched head-gauge normal-parameter data produced by the checked
finite-dimensional Witt normalizer and the checked Schur tail-coordinate
consumer. -/
def sourceOriented_headGaugeNormalParameterData
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  (sourceOriented_headGaugeWittData
    hd hrD hrn Head hGvar hHead hz).normalParameterData
    d n r hrD hrn Head hGvar hHead hz

namespace SourceOrientedHeadGaugeNormalParameterData

/-- The matched head-gauge normal-parameter head is invertible. -/
theorem head_det_unit
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    IsUnit D.p.head.det := by
  simpa [D.head_eq] using
    Head.factor_det_unit
      (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) hHead

/-- A matched head-gauge normal-parameter representative gives the required
shifted residual-tail membership. -/
theorem residualTail_mem_variety
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    {hGvar : G ∈ sourceOrientedGramVariety d n}
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  exact
    sourceOrientedSchurResidualTailData_mem_variety_of_eq_normalParameter
      d n r hrD hrn D.p D.invariant_eq D.head_eq
      (head_det_unit d n r hrD hrn Head hHead D)

/-- A matched head-gauge normal-parameter representative mechanically produces
the full Schur residual packet. -/
def schurResidualData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (D :
      SourceOrientedHeadGaugeNormalParameterData
        d n r hrD hrn hGvar Head) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem_headFactor
    d n r hrD hrn hGvar Head hHead
    (residualTail_mem_variety d n r hrD hrn Head hHead D)

end SourceOrientedHeadGaugeNormalParameterData

/-- If a proper complex Lorentz transformation carries one realizing source
tuple to a normal-parameter tuple whose head is the local gauge factor, then
the matched head-gauge normal-parameter data follows by oriented-invariant
preservation.

This conditional adapter is useful for local proofs that already carry an
explicit Lorentz-normalized tuple.  The unconditional head-gauge producer above
constructs that tuple from a source-variety representative. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛ :
      complexLorentzAction Λ z =
        sourceOrientedNormalParameterVector d n r hrD hrn p) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head where
  p := p
  invariant_eq := by
    calc
      G = sourceOrientedMinkowskiInvariant d n z := hz
      _ = sourceOrientedMinkowskiInvariant d n (complexLorentzAction Λ z) := by
        exact (sourceOrientedMinkowskiInvariant_complexLorentzAction
          (d := d) (n := n) Λ z).symm
      _ = sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p) := by
        rw [hΛ]
  head_eq := hhead

/-- Blockwise version of
`sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized`, using the
head/tail source-label split. -/
def sourceOriented_headGaugeNormalParameterData_of_lorentz_head_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead :
      Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar) =
        p.head)
    (Λ : ComplexLorentzGroup d)
    (hΛhead :
      ∀ a : Fin r,
        complexLorentzAction Λ z (finSourceHead hrn a) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceHead hrn a))
    (hΛtail :
      ∀ u : Fin (n - r),
        complexLorentzAction Λ z (finSourceTail hrn u) =
          sourceOrientedNormalParameterVector d n r hrD hrn p
            (finSourceTail hrn u)) :
    SourceOrientedHeadGaugeNormalParameterData
      d n r hrD hrn hGvar Head :=
  sourceOriented_headGaugeNormalParameterData_of_lorentz_normalized
    d n r hrD hrn hGvar Head hz hhead Λ (by
      ext i μ
      rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
      · exact congrFun (hΛhead a) μ
      · exact congrFun (hΛtail u) μ)

/-- The checked head-factor Witt normalizer proves that the explicit Schur
residual-tail datum lies on the shifted-tail oriented variety. -/
theorem sourceOrientedSchurResidualTailData_mem_variety_headFactor
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  let hGvar0 := hGvar
  rcases hGvar0 with ⟨z, hz⟩
  exact
    SourceOrientedHeadGaugeNormalParameterData.residualTail_mem_variety
      d n r hrD hrn Head hHead
      (sourceOriented_headGaugeNormalParameterData
        hd hrD hrn Head hGvar hHead hz.symm)

/-- The local head factor and checked Witt normalizer produce the full Schur
residual packet for a source-variety point whose selected head block lies in
the head-factor neighborhood. -/
def sourceOriented_schurResidualData_of_headFactor
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadFactorData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_tail_mem_headFactor
    d n r hrD hrn hGvar Head hHead
    (sourceOrientedSchurResidualTailData_mem_variety_headFactor
      hd hrD hrn Head hGvar hHead)

/-- Legacy full-gauge wrapper for the checked head-factor Witt normalizer. -/
theorem sourceOrientedSchurResidualTailData_mem_variety
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) :=
  sourceOrientedSchurResidualTailData_mem_variety_headFactor
    hd hrD hrn Head.toHeadFactorData hGvar hHead

/-- Sliced-gauge wrapper for the checked head-factor Witt normalizer. -/
theorem sourceOrientedSchurResidualTailData_mem_variety_headSliceGauge
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    sourceOrientedSchurResidualTailData d n r hrD hrn G
        ((Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar)).1) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) :=
  sourceOrientedSchurResidualTailData_mem_variety_headFactor
    hd hrD hrn Head.toHeadFactorData hGvar hHead

/-- Legacy full-gauge wrapper producing the full Schur residual packet. -/
def sourceOriented_schurResidualData_of_headGauge
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_headFactor
    hd hrD hrn Head.toHeadFactorData hGvar hHead

/-- Sliced-gauge wrapper producing the full Schur residual packet. -/
def sourceOriented_schurResidualData_of_headSliceGauge
    [NeZero d]
    (hd : 2 ≤ d)
    {n r : ℕ}
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadSliceGaugeData d r hrD)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U) :
    SourceOrientedSchurResidualData d n r hrD hrn G :=
  sourceOriented_schurResidualData_of_headFactor
    hd hrD hrn Head.toHeadFactorData hGvar hHead

end BHW
