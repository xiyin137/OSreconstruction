/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylRegularity

/-!
# Euclidean Weyl Probe Infrastructure

This file contains the finite coordinate-probe substrate for the scalar
regularization identity in the Euclidean Weyl representative route.  The probes
land in Banach spaces of bounded continuous functions, so the later pairing
identity can use ordinary Bochner integration after finite probe factorization
rather than a `SchwartzMap`-valued integral.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral
open scoped LineDeriv Convolution

namespace SCV

/-! ### Coordinate derivative probes -/

/-- Polynomial weight used to turn coordinate derivatives into bounded
continuous functions. -/
noncomputable def euclideanPolynomialWeight
    {ι : Type*} [Fintype ι]
    (k : ℕ) (x : EuclideanSpace ℝ ι) : ℂ :=
  (((1 : ℝ) + ‖x‖ ^ 2) ^ k : ℝ)

/-- The Euclidean polynomial weight has temperate growth, so multiplication by
it preserves Schwartz maps. -/
theorem euclideanPolynomialWeight_hasTemperateGrowth
    {ι : Type*} [Fintype ι]
    (k : ℕ) :
    (euclideanPolynomialWeight (ι := ι) k).HasTemperateGrowth := by
  unfold euclideanPolynomialWeight
  fun_prop

/-- Convert a tuple of coordinate labels into the corresponding tuple of
Euclidean basis vectors. -/
noncomputable def euclideanCoordinateDirs
    {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n → ι) :
    Fin n → EuclideanSpace ℝ ι :=
  fun j => EuclideanSpace.basisFun ι ℝ (u j)

/-- Iterated coordinate directional derivative as a continuous linear map on
Schwartz space. -/
noncomputable def euclideanIteratedCoordinateLineDerivCLM
    {ι : Type*} [Fintype ι] :
    (n : ℕ) → (Fin n → ι) →
      SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
        SchwartzMap (EuclideanSpace ℝ ι) ℂ
  | 0, _ => ContinuousLinearMap.id ℂ _
  | n + 1, u =>
      (LineDeriv.lineDerivOpCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ ι) ℂ)
        (EuclideanSpace.basisFun ι ℝ (u 0))).comp
          (euclideanIteratedCoordinateLineDerivCLM n (Fin.tail u))

/-- The recursive CLM agrees with Mathlib's iterated directional-derivative
notation. -/
theorem euclideanIteratedCoordinateLineDerivCLM_apply
    {ι : Type*} [Fintype ι] {n : ℕ}
    (u : Fin n → ι) (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanIteratedCoordinateLineDerivCLM n u f =
      ∂^{euclideanCoordinateDirs u} f := by
  induction n with
  | zero =>
      ext x
      simp [euclideanIteratedCoordinateLineDerivCLM,
        LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [euclideanIteratedCoordinateLineDerivCLM]
      change ∂_{EuclideanSpace.basisFun ι ℝ (u 0)}
          (euclideanIteratedCoordinateLineDerivCLM n (Fin.tail u) f) =
        ∂^{euclideanCoordinateDirs u} f
      rw [ih]
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rfl

/-- A weighted coordinate derivative probe landing in bounded continuous
functions. -/
noncomputable def euclideanWeightedLineDerivToBCFCLM
    {ι : Type*} [Fintype ι]
    (k n : ℕ) (u : Fin n → ι) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ :=
  (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (EuclideanSpace ℝ ι) ℂ).comp <|
    (SchwartzMap.smulLeftCLM ℂ (euclideanPolynomialWeight (ι := ι) k)).comp <|
      euclideanIteratedCoordinateLineDerivCLM n u

/-- Pointwise form of the weighted coordinate derivative probe. -/
theorem euclideanWeightedLineDerivToBCFCLM_apply
    {ι : Type*} [Fintype ι]
    (k n : ℕ) (u : Fin n → ι)
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (x : EuclideanSpace ℝ ι) :
    euclideanWeightedLineDerivToBCFCLM k n u f x =
      euclideanPolynomialWeight k x * (∂^{euclideanCoordinateDirs u} f) x := by
  rw [euclideanWeightedLineDerivToBCFCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (euclideanPolynomialWeight_hasTemperateGrowth (ι := ι) k),
    euclideanIteratedCoordinateLineDerivCLM_apply]
  simp [smul_eq_mul]

/-- The finite Banach probe space associated to a finite set of Schwartz
seminorm indices. -/
noncomputable abbrev EuclideanProbeSpace
    {ι : Type*} [Fintype ι] (s : Finset (ℕ × ℕ)) :=
  (p : ↑s.attach) →
    (Fin p.1.1.2 → ι) →
      BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ

/-- Probe a Schwartz map by all weighted coordinate derivatives in a finite
set of seminorm indices. -/
noncomputable def euclideanProbeCLM
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ)) :
    SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ]
      EuclideanProbeSpace (ι := ι) s :=
  ContinuousLinearMap.pi fun p : ↑s.attach =>
    ContinuousLinearMap.pi fun u : Fin p.1.1.2 → ι =>
      euclideanWeightedLineDerivToBCFCLM p.1.1.1 p.1.1.2 u

/-- Pointwise form of the finite coordinate probe map. -/
@[simp]
theorem euclideanProbeCLM_apply
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (p : ↑s.attach) (u : Fin p.1.1.2 → ι)
    (x : EuclideanSpace ℝ ι) :
    euclideanProbeCLM s f p u x =
      euclideanPolynomialWeight p.1.1.1 x *
        (∂^{euclideanCoordinateDirs u} f) x := by
  simp [euclideanProbeCLM, euclideanWeightedLineDerivToBCFCLM_apply]

/-! ### Coordinate domination of Schwartz seminorms -/

/-- Each coordinate of a Euclidean vector is bounded by its Euclidean norm. -/
theorem euclideanNorm_apply_le_norm
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  have hs : ‖x i‖ ^ 2 ≤ ∑ j : ι, ‖x j‖ ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (‖x j‖)) (Finset.mem_univ i)
  have hsq : ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq] using hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Expand a continuous multilinear map on Euclidean inputs into coordinate
values on the standard orthonormal basis. -/
theorem euclideanContinuousMultilinearMap_apply_eq_sum_coordinates
    {ι : Type*} [Fintype ι] {n : ℕ}
    (A : (EuclideanSpace ℝ ι) [×n]→L[ℝ] ℂ)
    (v : Fin n → EuclideanSpace ℝ ι) :
    A v =
      ∑ u : Fin n → ι,
        (∏ j : Fin n, (v j (u j) : ℝ)) •
          A (euclideanCoordinateDirs u) := by
  calc
    A v = A (fun j : Fin n =>
        ∑ i : ι, (v j i) • EuclideanSpace.basisFun ι ℝ i) := by
      apply congrArg A
      funext j
      exact ((EuclideanSpace.basisFun ι ℝ).sum_repr (v j)).symm
    _ = ∑ u : Fin n → ι,
        A (fun j : Fin n => (v j (u j)) • EuclideanSpace.basisFun ι ℝ (u j)) := by
      rw [ContinuousMultilinearMap.map_sum]
    _ = ∑ u : Fin n → ι,
        (∏ j : Fin n, (v j (u j) : ℝ)) •
          A (euclideanCoordinateDirs u) := by
      congr with u
      rw [ContinuousMultilinearMap.map_smul_univ]
      rfl

/-- The operator norm of a Euclidean continuous multilinear map is controlled
by the finite sum of its coordinate-basis values. -/
theorem euclideanContinuousMultilinearMap_norm_le_coordinate_sum
    {ι : Type*} [Fintype ι] (n : ℕ)
    (A : (EuclideanSpace ℝ ι) [×n]→L[ℝ] ℂ) :
    ‖A‖ ≤
      Finset.univ.sum
        (fun u : Fin n → ι => ‖A (euclideanCoordinateDirs u)‖) := by
  let M : ℝ := Finset.univ.sum
    (fun u : Fin n → ι => ‖A (euclideanCoordinateDirs u)‖)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun u _ => norm_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A) hM_nonneg ?_
  intro v
  have hexp := euclideanContinuousMultilinearMap_apply_eq_sum_coordinates A v
  calc
    ‖A v‖ = ‖∑ u : Fin n → ι,
        (∏ j : Fin n, (v j (u j) : ℝ)) •
          A (euclideanCoordinateDirs u)‖ := by
      rw [hexp]
    _ ≤ ∑ u : Fin n → ι,
        ‖(∏ j : Fin n, (v j (u j) : ℝ)) •
          A (euclideanCoordinateDirs u)‖ := norm_sum_le _ _
    _ ≤ ∑ u : Fin n → ι,
        (∏ j : Fin n, ‖v j‖) * ‖A (euclideanCoordinateDirs u)‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod]
      exact Finset.prod_le_prod
        (fun j _ => norm_nonneg ((v j) (u j)))
        (fun j _ => euclideanNorm_apply_le_norm (v j) (u j))
    _ = M * ∏ j : Fin n, ‖v j‖ := by
      dsimp [M]
      rw [Finset.sum_mul]
      congr with u
      ring

/-- The polynomial weight dominates the ordinary Euclidean power
`‖x‖ ^ k`. -/
theorem euclideanNorm_pow_le_polynomialWeight_norm
    {ι : Type*} [Fintype ι]
    (k : ℕ) (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ k ≤ ‖euclideanPolynomialWeight k x‖ := by
  rw [euclideanPolynomialWeight, Complex.norm_real]
  have h1 : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - (1 / 2 : ℝ))]
  calc
    ‖x‖ ^ k ≤ (1 + ‖x‖ ^ 2) ^ k := by
      exact pow_le_pow_left₀ (norm_nonneg _) h1 k
    _ = ‖((1 + ‖x‖ ^ 2) ^ k : ℝ)‖ := by
      rw [Real.norm_of_nonneg]
      positivity

/-- Euclidean Schwartz seminorms are controlled by the finite family of
weighted coordinate derivative probes. -/
theorem euclideanSchwartzSeminorm_le_coordinateProbeNorm
    {ι : Type*} [Fintype ι]
    (k n : ℕ) (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap.seminorm ℝ k n f ≤
      Finset.univ.sum
        (fun u : Fin n → ι => ‖euclideanWeightedLineDerivToBCFCLM k n u f‖) := by
  let M : ℝ := Finset.univ.sum
    (fun u : Fin n → ι => ‖euclideanWeightedLineDerivToBCFCLM k n u f‖)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun u _ => norm_nonneg _
  refine SchwartzMap.seminorm_le_bound ℝ k n f hM_nonneg ?_
  intro x
  have hnorm := euclideanContinuousMultilinearMap_norm_le_coordinate_sum n
    (iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x‖
        ≤ ‖x‖ ^ k *
          Finset.univ.sum
            (fun u : Fin n → ι =>
              ‖iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x
                (euclideanCoordinateDirs u)‖) := by
      exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg (norm_nonneg _) k)
    _ = Finset.univ.sum
          (fun u : Fin n → ι =>
            ‖x‖ ^ k *
              ‖iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x
                (euclideanCoordinateDirs u)‖) := by
      rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum
          (fun u : Fin n → ι => ‖euclideanWeightedLineDerivToBCFCLM k n u f‖) := by
      apply Finset.sum_le_sum
      intro u hu
      have hline :
          (∂^{euclideanCoordinateDirs u} f) x =
            iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x
              (euclideanCoordinateDirs u) := by
        exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
      calc
        ‖x‖ ^ k *
            ‖iteratedFDeriv ℝ n (f : EuclideanSpace ℝ ι → ℂ) x
              (euclideanCoordinateDirs u)‖
            ≤ ‖euclideanPolynomialWeight k x‖ *
                ‖(∂^{euclideanCoordinateDirs u} f) x‖ := by
          rw [hline]
          exact mul_le_mul_of_nonneg_right
            (euclideanNorm_pow_le_polynomialWeight_norm k x)
            (norm_nonneg _)
        _ = ‖euclideanWeightedLineDerivToBCFCLM k n u f x‖ := by
          rw [euclideanWeightedLineDerivToBCFCLM_apply, norm_mul]
        _ ≤ ‖euclideanWeightedLineDerivToBCFCLM k n u f‖ := by
          simpa using
            (BoundedContinuousFunction.norm_coe_le_norm
              (euclideanWeightedLineDerivToBCFCLM k n u f) x)
    _ = M := rfl

/-! ### Finite probe factorization of Schwartz functionals -/

/-- A continuous Euclidean Schwartz functional is bounded by finitely many
Schwartz seminorms. -/
theorem euclideanSchwartzFunctional_bound
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        ‖T φ‖ ≤ (C • s.sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ)) φ := by
  let q : Seminorm ℂ (SchwartzMap (EuclideanSpace ℝ ι) ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ => ‖T φ‖)
    simpa [q, Seminorm.comp_apply, coe_normSeminorm] using
      continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ) q hq_cont
  refine ⟨s, C, hC, ?_⟩
  intro φ
  simpa [q, Seminorm.comp_apply, coe_normSeminorm] using hbound φ

/-- Each selected Euclidean Schwartz seminorm is bounded by the norm of the
finite probe packet. -/
theorem euclideanSchwartzSeminorm_le_probeNorm
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ)) (p : ↑s.attach)
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f ≤
      Fintype.card (Fin p.1.1.2 → ι) *
        ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
  calc
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f
        ≤ Finset.univ.sum
            (fun u : Fin p.1.1.2 → ι =>
              ‖euclideanWeightedLineDerivToBCFCLM p.1.1.1 p.1.1.2 u f‖) :=
      euclideanSchwartzSeminorm_le_coordinateProbeNorm p.1.1.1 p.1.1.2 f
    _ ≤ Finset.univ.sum
        (fun _u : Fin p.1.1.2 → ι =>
          ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖) := by
      apply Finset.sum_le_sum
      intro u hu
      calc
        ‖euclideanWeightedLineDerivToBCFCLM p.1.1.1 p.1.1.2 u f‖
            = ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s) p u‖ := by
              simp [euclideanProbeCLM]
        _ ≤ ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s) p‖ := by
              simpa using
                (norm_le_pi_norm
                  ((euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s) p) u)
        _ ≤ ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
              simpa using
                (norm_le_pi_norm
                  (euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s) p)
    _ = Fintype.card (Fin p.1.1.2 → ι) *
        ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
      simp

/-- A continuous Euclidean Schwartz functional is bounded by the norm of one
finite Banach probe packet. -/
theorem euclideanSchwartzFunctional_bound_by_probeNorm
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        ‖T f‖ ≤ C * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
  classical
  obtain ⟨s, C0, _hC0, hbound⟩ := euclideanSchwartzFunctional_bound T
  let D : ℝ := ∑ p ∈ s, (Fintype.card (Fin p.2 → ι) : ℝ)
  let C : ℝ := (C0 : ℝ) * D
  refine ⟨s, C, by positivity, ?_⟩
  intro f
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ)) f ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p) f := by
    exact Seminorm.le_def.mp
      (Seminorm.finset_sup_le_sum
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ) s) f
  have hsum_apply_all :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p) f =
          ∑ p ∈ s', schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p f := by
    intro s'
    induction s' using Finset.induction with
    | empty => simp
    | insert a s' ha ih => simp [Finset.sum_insert, ha, ih]
  have hsum_apply :
      (∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p) f =
        ∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p f :=
    hsum_apply_all s
  have hsum_probe :
      ∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p f ≤
        D * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
    calc
      ∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p f
          ≤ ∑ p ∈ s,
              (Fintype.card (Fin p.2 → ι) : ℝ) *
                ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
        refine Finset.sum_le_sum ?_
        intro a ha
        let p : ↑s.attach := ⟨⟨a, ha⟩, by simp⟩
        simpa [schwartzSeminormFamily, p] using
          euclideanSchwartzSeminorm_le_probeNorm s p f
      _ = D * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
        dsimp [D]
        rw [Finset.sum_mul]
  calc
    ‖T f‖ ≤ (C0 • s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ)) f := hbound f
    _ = (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ)) f := by rfl
    _ ≤ (C0 : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p) f) := by
      exact mul_le_mul_of_nonneg_left hsup_sum C0.coe_nonneg
    _ = (C0 : ℝ) * (∑ p ∈ s, schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ p f) := by
      rw [hsum_apply]
    _ ≤ (C0 : ℝ) * (D * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖) := by
      exact mul_le_mul_of_nonneg_left hsum_probe C0.coe_nonneg
    _ = C * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := by
      ring

private noncomputable def euclideanRangeLiftLinear
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker :
      LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap ≤
        LinearMap.ker T.toLinearMap) :
    LinearMap.range (euclideanProbeCLM (ι := ι) s).toLinearMap →ₗ[ℂ] ℂ :=
  ((LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap).liftQ T.toLinearMap
    hker).comp
    ((euclideanProbeCLM (ι := ι) s).toLinearMap.quotKerEquivRange.symm.toLinearMap)

private theorem euclideanRangeLiftLinear_apply
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker :
      LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap ≤
        LinearMap.ker T.toLinearMap)
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    euclideanRangeLiftLinear T s hker
        ⟨euclideanProbeCLM s f,
          LinearMap.mem_range_self (euclideanProbeCLM (ι := ι) s).toLinearMap f⟩ = T f := by
  change
    ((LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap).liftQ T.toLinearMap
      hker)
        (((euclideanProbeCLM (ι := ι) s).toLinearMap.quotKerEquivRange.symm)
          ⟨euclideanProbeCLM s f,
            LinearMap.mem_range_self (euclideanProbeCLM (ι := ι) s).toLinearMap f⟩) = T f
  have hsymm :
      ((euclideanProbeCLM (ι := ι) s).toLinearMap.quotKerEquivRange.symm)
          ⟨euclideanProbeCLM s f,
            LinearMap.mem_range_self (euclideanProbeCLM (ι := ι) s).toLinearMap f⟩ =
        (LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap).mkQ f := by
    simpa using
      (LinearMap.quotKerEquivRange_symm_apply_image
        ((euclideanProbeCLM (ι := ι) s).toLinearMap) f
        (LinearMap.mem_range_self (euclideanProbeCLM (ι := ι) s).toLinearMap f))
  rw [hsymm]
  simp

private theorem euclideanRangeLiftLinear_bound
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (C : ℝ)
    (hbound : ∀ f : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
      ‖T f‖ ≤ C * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖)
    (hker :
      LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap ≤
        LinearMap.ker T.toLinearMap) :
    ∀ y, ‖euclideanRangeLiftLinear T s hker y‖ ≤ C * ‖y‖ := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨f, rfl⟩
  simpa [euclideanRangeLiftLinear_apply] using hbound f

/-- Any continuous Euclidean Schwartz functional factors through finitely many
weighted coordinate-derivative probes landing in a Banach product of bounded
continuous functions. -/
theorem euclideanSchwartzFunctional_exists_probe_factorization
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ G : EuclideanProbeSpace (ι := ι) s →L[ℂ] ℂ,
      T = G.comp (euclideanProbeCLM s) := by
  classical
  obtain ⟨s, C, _hC_nonneg, hbound⟩ := euclideanSchwartzFunctional_bound_by_probeNorm T
  have hker :
      LinearMap.ker (euclideanProbeCLM (ι := ι) s).toLinearMap ≤
        LinearMap.ker T.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply norm_eq_zero.mp
    apply le_antisymm
    · calc
        ‖T f‖ ≤ C * ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ := hbound f
        _ = 0 := by
          have hfnorm :
              ‖(euclideanProbeCLM s f : EuclideanProbeSpace (ι := ι) s)‖ = 0 := by
            simpa using congrArg norm hf
          rw [hfnorm, mul_zero]
    · exact norm_nonneg _
  let FrangeLin :
      LinearMap.range (euclideanProbeCLM (ι := ι) s).toLinearMap →ₗ[ℂ] ℂ :=
    euclideanRangeLiftLinear T s hker
  let Frange :
      StrongDual ℂ (LinearMap.range (euclideanProbeCLM (ι := ι) s).toLinearMap) :=
    FrangeLin.mkContinuous C (euclideanRangeLiftLinear_bound T s C hbound hker)
  obtain ⟨G, hGext, _⟩ :=
    exists_extension_norm_eq
      (LinearMap.range (euclideanProbeCLM (ι := ι) s).toLinearMap) Frange
  refine ⟨s, G, ?_⟩
  ext f
  have hmem :
      euclideanProbeCLM s f ∈
        LinearMap.range (euclideanProbeCLM (ι := ι) s).toLinearMap :=
    LinearMap.mem_range_self (euclideanProbeCLM (ι := ι) s).toLinearMap f
  change T f = G (euclideanProbeCLM s f)
  calc
    T f = FrangeLin ⟨euclideanProbeCLM s f, hmem⟩ := by
      exact (euclideanRangeLiftLinear_apply T s hker f).symm
    _ = Frange ⟨euclideanProbeCLM s f, hmem⟩ := by
      rfl
    _ = G (euclideanProbeCLM s f) := by
      symm
      exact hGext ⟨euclideanProbeCLM s f, hmem⟩

end SCV
