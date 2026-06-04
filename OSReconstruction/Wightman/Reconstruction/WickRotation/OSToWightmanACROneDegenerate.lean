/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReduced

/-!
# Degenerate ACR(1) Product-Tensor Witnesses

This file closes the `k = 0` and `k = 1` branches of the W4
`ACR(1)` product-tensor witness.  The remaining positive-length
multi-point branch stays in `OSToWightman.lean`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal LineDeriv
open BigOperators Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

variable {d : ℕ} [NeZero d]

/-- The zero-point case of the `ACR(1)` product-tensor witness is just the
OS-II normalization `S₀(1)=1`, together with the empty-product volume
normalization. -/
theorem exists_acrOne_productTensor_witness_zero {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (S_prod : (Fin 0 → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d 0 1) ∧
      (∀ (fs : Fin 0 → SchwartzSpacetime d)
          (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S 0 ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d 0,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x) ∧
      (∀ (σ : Equiv.Perm (Fin 0)) (z : Fin 0 → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z) ∧
      (∀ (z : Fin 0 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) ∧
      (∀ (x : NPointDomain d 0) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S_prod (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S_prod (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d 0 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  let S_prod : (Fin 0 → Fin (d + 1) → ℂ) → ℂ := fun _ => 1
  refine ⟨S_prod, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro fs hvanish
    have hS : OS.S 0 ⟨SchwartzMap.productTensor fs, hvanish⟩ =
        (⟨SchwartzMap.productTensor fs, hvanish⟩ : ZeroDiagonalSchwartz d 0).1 0 :=
      lgc.normalized_zero ⟨SchwartzMap.productTensor fs, hvanish⟩
    have hvol_real :
        ((MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 0)).real
            Set.univ : ℝ) = 1 := by
      rw [MeasureTheory.Measure.real]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 0))
              Set.univ = 1 := by
        rw [MeasureTheory.volume_pi]
        exact
          MeasureTheory.Measure.pi_empty_univ
            (μ := fun _ : Fin 0 =>
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (d + 1) → ℝ)))
            (β := fun _ : Fin 0 => Fin (d + 1) → ℝ)
      rw [hvol]
      norm_num
    rw [hS]
    calc
      ((⟨SchwartzMap.productTensor fs, hvanish⟩ :
          ZeroDiagonalSchwartz d 0).1 0) = (1 : ℂ) := by
            simp
      _ =
          ∫ x : NPointDomain d 0,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x := by
            simp [S_prod, hvol_real]
  · intro σ z
    rfl
  · intro z a
    rfl
  · intro x ε hε
    simp [S_prod]
  · refine ⟨1, 0, by norm_num, ?_⟩
    intro z hz
    simp [S_prod]

private theorem productTensor_fin_one_eq_onePoint
    (fs : Fin 1 → SchwartzSpacetime d) :
    SchwartzMap.productTensor fs = onePointToFin1CLM d (fs 0) := by
  ext x
  simp [SchwartzMap.productTensor_apply, onePointToFin1CLM_apply]

private noncomputable def schwingerOneFlatCLM
    (OS : OsterwalderSchraderAxioms d) :
    SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS 1).comp
    ((unflattenSchwartzNPoint (d := d) (n := 1)).codRestrict
      (zeroDiagonalSubmodule d 1)
      (fun F => VanishesToInfiniteOrderOnCoincidence.one
        (d := d) ((unflattenSchwartzNPoint (d := d) (n := 1)) F)))

private theorem schwingerOneFlatCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (F : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ) :
    schwingerOneFlatCLM (d := d) OS F =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical
        ((unflattenSchwartzNPoint (d := d) (n := 1)) F)) := by
  dsimp [schwingerOneFlatCLM, OsterwalderSchraderAxioms.schwingerCLM]
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := (unflattenSchwartzNPoint (d := d) (n := 1)) F)
    (VanishesToInfiniteOrderOnCoincidence.one
      (d := d) ((unflattenSchwartzNPoint (d := d) (n := 1)) F))]
  congr 1

private theorem schwingerOneFlatCLM_translationInvariant
    (OS : OsterwalderSchraderAxioms d) :
    OSReconstruction.IsTranslationInvariantSchwartzCLM
      (schwingerOneFlatCLM (d := d) OS) := by
  intro a
  ext F
  let avec : SpacetimeDim d := fun μ =>
    a (finProdFinEquiv ((0 : Fin 1), μ))
  have hpoint :
      ∀ x : NPointDomain d 1,
        ((unflattenSchwartzNPoint (d := d) (n := 1))
            (SCV.translateSchwartz a F)) x =
          ((unflattenSchwartzNPoint (d := d) (n := 1)) F)
            (fun i => x i + avec) := by
    intro x
    simp only [unflattenSchwartzNPoint_apply, SCV.translateSchwartz_apply]
    congr 1
    ext q
    change (flattenCLEquivReal 1 (d + 1) x + a) q =
      flattenCLEquivReal 1 (d + 1) (fun i => x i + avec) q
    rw [Pi.add_apply, flattenCLEquivReal_apply, flattenCLEquivReal_apply]
    have hfst : (finProdFinEquiv.symm q).1 = (0 : Fin 1) :=
      Subsingleton.elim _ _
    have hq : q = finProdFinEquiv ((0 : Fin 1), (finProdFinEquiv.symm q).2) := by
      have hp :
          finProdFinEquiv.symm q =
            ((0 : Fin 1), (finProdFinEquiv.symm q).2) := by
        exact Prod.ext hfst rfl
      calc
        q = finProdFinEquiv (finProdFinEquiv.symm q) :=
          (finProdFinEquiv.apply_symm_apply q).symm
        _ = finProdFinEquiv ((0 : Fin 1), (finProdFinEquiv.symm q).2) := by
          rw [hp]
    rw [hfst]
    change x 0 (finProdFinEquiv.symm q).2 + a q =
      x 0 (finProdFinEquiv.symm q).2 +
        a (finProdFinEquiv ((0 : Fin 1), (finProdFinEquiv.symm q).2))
    rw [← hq]
  change schwingerOneFlatCLM (d := d) OS (SCV.translateSchwartz a F) =
    schwingerOneFlatCLM (d := d) OS F
  rw [schwingerOneFlatCLM_apply, schwingerOneFlatCLM_apply]
  exact
    (OS.E1_translation_invariant 1 avec
      (ZeroDiagonalSchwartz.ofClassical
        ((unflattenSchwartzNPoint (d := d) (n := 1)) F))
      (ZeroDiagonalSchwartz.ofClassical
        ((unflattenSchwartzNPoint (d := d) (n := 1))
          (SCV.translateSchwartz a F)))
      (by
        intro x
        rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
          (f := (unflattenSchwartzNPoint (d := d) (n := 1))
            (SCV.translateSchwartz a F))
          (VanishesToInfiniteOrderOnCoincidence.one
            (d := d) ((unflattenSchwartzNPoint (d := d) (n := 1))
              (SCV.translateSchwartz a F)))]
        rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
          (f := (unflattenSchwartzNPoint (d := d) (n := 1)) F)
          (VanishesToInfiniteOrderOnCoincidence.one
            (d := d) ((unflattenSchwartzNPoint (d := d) (n := 1)) F))]
        exact hpoint x)).symm

private theorem integral_onePointToFin1_normalizedCutoff
    (d : ℕ) [NeZero d] :
    ∫ x : NPointDomain d 1,
      (onePointToFin1CLM d (BHW.normalizedCutoffOfBump d).toSchwartz :
        SchwartzNPoint d 1) x = 1 := by
  let χ : SchwartzSpacetime d := (BHW.normalizedCutoffOfBump d).toSchwartz
  have hcomp :=
    MeasureTheory.MeasurePreserving.integral_comp'
      (MeasureTheory.volume_preserving_funUnique (Fin 1) (SpacetimeDim d))
      (fun y : SpacetimeDim d => χ y)
  calc
    ∫ x : NPointDomain d 1,
        (onePointToFin1CLM d (BHW.normalizedCutoffOfBump d).toSchwartz :
          SchwartzNPoint d 1) x =
        ∫ x : Fin 1 → SpacetimeDim d, χ (x 0) := by
          rfl
    _ = ∫ y : SpacetimeDim d, χ y := by
          simpa [χ, ContinuousLinearEquiv.coe_funUnique] using hcomp
    _ = 1 := by
          exact (BHW.normalizedCutoffOfBump d).integral_eq_one

private theorem integral_flattenSchwartzNPoint_flat {n : ℕ}
    (f : SchwartzNPoint d n) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (n * (d + 1)) → ℝ)))
        (flattenSchwartzNPoint (d := d) f)
      =
    ∫ x : NPointDomain d n, f x := by
  rw [SchwartzMap.integralCLM_apply]
  simpa [flattenSchwartzNPoint_apply] using
    integral_flatten_change_of_variables n (d + 1) (flattenSchwartzNPoint (d := d) f)

private theorem integral_osConj_eq_conj_integral
    (f : SchwartzNPoint d 1) :
    ∫ x : NPointDomain d 1, f.osConj x =
      starRingEnd ℂ (∫ x : NPointDomain d 1, f x) := by
  let θ : NPointDomain d 1 ≃ᵐ NPointDomain d 1 :=
    { toEquiv :=
        { toFun := timeReflectionN (d := d) (n := 1)
          invFun := timeReflectionN (d := d) (n := 1)
          left_inv := by
            intro x
            ext i μ
            by_cases hμ : μ = 0
            · simp [timeReflectionN, timeReflection, hμ]
            · simp [timeReflectionN, timeReflection, hμ]
          right_inv := by
            intro x
            ext i μ
            by_cases hμ : μ = 0
            · simp [timeReflectionN, timeReflection, hμ]
            · simp [timeReflectionN, timeReflection, hμ] }
      measurable_toFun :=
        (timeReflectionN_measurePreserving (d := d) (n := 1)).measurable
      measurable_invFun :=
        (timeReflectionN_measurePreserving (d := d) (n := 1)).measurable }
  have hθmp :
      MeasureTheory.MeasurePreserving (θ : NPointDomain d 1 → NPointDomain d 1)
        MeasureTheory.volume MeasureTheory.volume := by
    simpa [θ] using timeReflectionN_measurePreserving (d := d) (n := 1)
  have hcomp :
      ∫ x : NPointDomain d 1, f (timeReflectionN d x) =
        ∫ x : NPointDomain d 1, f x :=
    MeasureTheory.MeasurePreserving.integral_comp'
      hθmp
      (fun x : NPointDomain d 1 => f x)
  calc
    ∫ x : NPointDomain d 1, f.osConj x =
        ∫ x : NPointDomain d 1,
          starRingEnd ℂ (f (timeReflectionN d x)) := by
          rfl
    _ = starRingEnd ℂ
        (∫ x : NPointDomain d 1, f (timeReflectionN d x)) := by
          exact _root_.integral_conj
    _ = starRingEnd ℂ (∫ x : NPointDomain d 1, f x) := by
          rw [hcomp]

private theorem schwingerOneFlatCLM_const_real
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ)
    (hc : schwingerOneFlatCLM (d := d) OS =
      c • (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ)))) :
    starRingEnd ℂ c = c := by
  let f0 : SchwartzNPoint d 1 :=
    onePointToFin1CLM d (BHW.normalizedCutoffOfBump d).toSchwartz
  let F0 : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f0
  let F0R : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ :=
    flattenSchwartzNPoint (d := d) f0.osConj
  have hunflat0 :
      (unflattenSchwartzNPoint (d := d) (n := 1)) F0 = f0 := by
    ext x
    simp [F0, unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hunflatR :
      (unflattenSchwartzNPoint (d := d) (n := 1)) F0R = f0.osConj := by
    ext x
    simp [F0R, unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hI0 :
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ))) F0 = 1 := by
    change (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ)))
        (flattenSchwartzNPoint (d := d) f0) = 1
    rw [integral_flattenSchwartzNPoint_flat]
    exact integral_onePointToFin1_normalizedCutoff d
  have hIR :
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ))) F0R = 1 := by
    change (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume :
          MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ)))
        (flattenSchwartzNPoint (d := d) f0.osConj) = 1
    rw [integral_flattenSchwartzNPoint_flat]
    rw [integral_osConj_eq_conj_integral]
    rw [integral_onePointToFin1_normalizedCutoff d]
    simp
  have hT0 : schwingerOneFlatCLM (d := d) OS F0 = c := by
    have := congrArg
      (fun T : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ => T F0) hc
    simpa [ContinuousLinearMap.smul_apply, hI0, smul_eq_mul] using this
  have hTR : schwingerOneFlatCLM (d := d) OS F0R = c := by
    have := congrArg
      (fun T : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ => T F0R) hc
    simpa [ContinuousLinearMap.smul_apply, hIR, smul_eq_mul] using this
  have hrealT :
      starRingEnd ℂ (schwingerOneFlatCLM (d := d) OS F0) =
        schwingerOneFlatCLM (d := d) OS F0R := by
    rw [schwingerOneFlatCLM_apply, schwingerOneFlatCLM_apply, hunflat0, hunflatR]
    exact OS.E0_reality 1
      (ZeroDiagonalSchwartz.ofClassical f0)
      (ZeroDiagonalSchwartz.ofClassical f0.osConj)
      (by
        intro x
        rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
          (f := f0) (VanishesToInfiniteOrderOnCoincidence.one (d := d) f0)]
        rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
          (f := f0.osConj)
          (VanishesToInfiniteOrderOnCoincidence.one (d := d) f0.osConj)]
        exact SchwartzNPoint.osConj_apply f0 x)
  calc
    starRingEnd ℂ c = starRingEnd ℂ (schwingerOneFlatCLM (d := d) OS F0) := by
      rw [hT0]
    _ = schwingerOneFlatCLM (d := d) OS F0R := hrealT
    _ = c := hTR

/-- The one-point case of the `ACR(1)` product-tensor witness is the classical
translation-invariant distribution theorem: a one-point Schwinger functional is
a real scalar multiple of Lebesgue integration. -/
theorem exists_acrOne_productTensor_witness_one {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) :
    ∃ (S_prod : (Fin 1 → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_prod (AnalyticContinuationRegion d 1 1) ∧
      (∀ (fs : Fin 1 → SchwartzSpacetime d)
          (hvanish : VanishesToInfiniteOrderOnCoincidence (SchwartzMap.productTensor fs)),
        OS.S 1 ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          ∫ x : NPointDomain d 1,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x) ∧
      (∀ (σ : Equiv.Perm (Fin 1)) (z : Fin 1 → Fin (d + 1) → ℂ),
        S_prod (fun j => z (σ j)) = S_prod z) ∧
      (∀ (z : Fin 1 → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
        S_prod (fun j => z j + a) = S_prod z) ∧
      (∀ (x : NPointDomain d 1) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (S_prod (fun j μ =>
            ↑(x j μ) +
              ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) =
        S_prod (fun j μ =>
          ↑(x j μ) -
            ε * ↑(if μ = 0 then (↑(j : ℕ) + 1 : ℝ) else 0) * Complex.I)) ∧
      ∃ (C_bd : ℝ) (N : ℕ),
        0 < C_bd ∧
        ∀ z ∈ AnalyticContinuationRegion d 1 1,
          ‖S_prod z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  obtain ⟨c, hc⟩ :=
    OSReconstruction.exists_eq_const_integralCLM_of_translationInvariant
      (schwingerOneFlatCLM (d := d) OS)
      (schwingerOneFlatCLM_translationInvariant (d := d) OS)
  have hc_real : starRingEnd ℂ c = c :=
    schwingerOneFlatCLM_const_real (d := d) OS c hc
  let S_prod : (Fin 1 → Fin (d + 1) → ℂ) → ℂ := fun _ => c
  refine ⟨S_prod, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro fs hvanish
    have hflat :
        (unflattenSchwartzNPoint (d := d) (n := 1))
            (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs)) =
          SchwartzMap.productTensor fs := by
      ext x
      simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
    have hT_eval :
        schwingerOneFlatCLM (d := d) OS
            (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs)) =
          c *
            (SchwartzMap.integralCLM ℂ
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ)))
              (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs)) := by
      have := congrArg
        (fun T : SchwartzMap (Fin (1 * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
          T (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs))) hc
      simpa [ContinuousLinearMap.smul_apply, smul_eq_mul] using this
    have hleft :
        schwingerOneFlatCLM (d := d) OS
            (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs)) =
          OS.S 1 ⟨SchwartzMap.productTensor fs, hvanish⟩ := by
      rw [schwingerOneFlatCLM_apply, hflat]
      rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
        (f := SchwartzMap.productTensor fs) hvanish]
    have hintegral_flat :
        (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume :
              MeasureTheory.Measure (Fin (1 * (d + 1)) → ℝ)))
            (flattenSchwartzNPoint (d := d) (SchwartzMap.productTensor fs)) =
          ∫ x : NPointDomain d 1, (SchwartzMap.productTensor fs) x :=
      integral_flattenSchwartzNPoint_flat (d := d) (SchwartzMap.productTensor fs)
    calc
      OS.S 1 ⟨SchwartzMap.productTensor fs, hvanish⟩ =
          c * ∫ x : NPointDomain d 1, (SchwartzMap.productTensor fs) x := by
        rw [← hintegral_flat, ← hleft]
        exact hT_eval
      _ =
          ∫ x : NPointDomain d 1,
            S_prod (fun j => wickRotatePoint (x j)) *
              (SchwartzMap.productTensor fs) x := by
        exact (integral_const_mul
          (μ := (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d 1)))
          c (fun x : NPointDomain d 1 => (SchwartzMap.productTensor fs) x)).symm
  · intro σ z
    rfl
  · intro z a
    rfl
  · intro x ε hε
    simpa [S_prod] using hc_real
  · refine ⟨max ‖c‖ 1, 0, ?_, ?_⟩
    · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    · intro z hz
      simp [S_prod]
