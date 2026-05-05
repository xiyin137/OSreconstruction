/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.HeadFiberAntiderivInterval

/-!
# Head-fiber antiderivative decay and Schwartz packaging

This file finishes the pure SCV extraction of the one-coordinate
head-fiber antiderivative.  The input is a Schwartz function whose head
slices have zero integral.  The output is the Schwartz primitive whose
head directional derivative recovers the input.
-/

noncomputable section

open scoped SchwartzMap Topology
open MeasureTheory SchwartzMap LineDeriv

namespace SCV

/-- The zero-slice condition is preserved by differentiating in a pure tail
direction. This is the parameter-preservation input needed for the eventual
decay induction on the head-fiber antiderivative. -/
theorem zeroSlice_lineDerivOp_tailInsert {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (w : Fin n → ℝ) :
    ∀ y : Fin n → ℝ,
      ∫ t : ℝ, (∂_{tailInsertCLM n w} F) (Fin.cons t y) = 0 := by
  intro y
  have hzeroFun : sliceIntegralRaw F = 0 := by
    ext y'
    exact hzero y'
  have hline_zero : lineDeriv ℝ (sliceIntegralRaw F) y w = 0 := by
    rw [hzeroFun]
    change lineDeriv ℝ (fun _ : Fin n → ℝ => (0 : ℂ)) y w = 0
    rw [((hasFDerivAt_const (0 : ℂ) y).hasLineDerivAt w).lineDeriv]
    simp
  have hline_formula :
      lineDeriv ℝ (sliceIntegralRaw F) y w =
        sliceIntegralRaw (∂_{tailInsertCLM n w} F) y := by
    have h_int :
        Integrable
          (fun x : ℝ =>
            (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons x y)).comp (tailInsertCLM n))
          volume := by
      let C : ℝ :=
        (4 : ℝ) * ((Finset.Iic (2, 1)).sup
          (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
      have hmajor_int :
          Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
        simpa [C, mul_comm, mul_left_comm, mul_assoc] using
          (integrable_inv_one_add_sq.const_mul C)
      have hpath : Continuous fun x : ℝ => (Fin.cons x y : Fin (n + 1) → ℝ) := by
        classical
        refine continuous_pi ?_
        intro j
        refine Fin.cases ?_ ?_ j
        · simpa using (continuous_id : Continuous fun x : ℝ => x)
        · intro i
          simpa using (continuous_const : Continuous fun _ : ℝ => y i)
      have hcont :
          Continuous
            (fun x : ℝ =>
              (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons x y)).comp (tailInsertCLM n)) := by
        exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
      refine hmajor_int.mono' hcont.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun x =>
        (norm_fderiv_sliceSection_le_inv_one_add_sq F y x).trans_eq (by simp [C]))
    rw [((hasFDerivAt_sliceIntegralRaw F y).hasLineDerivAt w).lineDeriv]
    rw [ContinuousLinearMap.integral_apply h_int]
    simp [sliceIntegralRaw, SchwartzMap.lineDerivOp_apply_eq_fderiv, tailInsertCLM_apply]
  rw [hline_formula] at hline_zero
  simpa [sliceIntegralRaw] using hline_zero

/-! ## Head-fiber antiderivative decay and Schwartz packaging -/

/-- Evaluating the derivative of the fixed `(-∞, 0]` slice piece on a pure tail
vector gives the same slice piece for the tail-differentiated Schwartz map. -/
theorem fderiv_iicZeroSlice_comp_tail_tailInsert_eq {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) (w : Fin n → ℝ) :
    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x
        (tailInsertCLM n w) =
      iicZeroSlice (∂_{tailInsertCLM n w} F) (Fin.tail x) := by
  have hcomp := (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
    ((tailCLM n).hasFDerivAt)
  have h_int :
      Integrable
        (fun t : ℝ =>
          (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
            (tailInsertCLM n))
        (MeasureTheory.volume.restrict (Set.Iic (0 : ℝ))) := by
    let C : ℝ :=
      (4 : ℝ) * ((Finset.Iic (2, 1)).sup
        (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
    have hmajor_int :
        Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [C, mul_comm, mul_left_comm, mul_assoc] using
        (integrable_inv_one_add_sq.const_mul C)
    have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
      classical
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa using (continuous_id : Continuous fun t : ℝ => t)
      · intro i
        simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
    have hcont :
        Continuous
          (fun t : ℝ =>
            (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
              (tailInsertCLM n)) := by
      exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
    refine hmajor_int.restrict.mono' hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun t =>
      (norm_fderiv_sliceSection_le_inv_one_add_sq F (Fin.tail x) t).trans_eq (by simp [C]))
  change (fderiv ℝ (iicZeroSlice F ∘ Fin.tail) x) (tailInsertCLM n w) =
      iicZeroSlice (∂_{tailInsertCLM n w} F) (Fin.tail x)
  rw [hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.integral_apply h_int]
  simp [iicZeroSlice, SchwartzMap.lineDerivOp_apply_eq_fderiv, tailInsertCLM_apply,
    tailCLM_apply]

/-- Evaluating the derivative of the variable-limit interval piece on a pure
tail vector gives the interval piece for the tail-differentiated Schwartz map. -/
theorem fderiv_intervalPiece_tailInsert_eq {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x : Fin (n + 1) → ℝ) (w : Fin n → ℝ) :
    fderiv ℝ (intervalPiece F) x (tailInsertCLM n w) =
      intervalPiece (∂_{tailInsertCLM n w} F) x := by
  let v : Fin (n + 1) → ℝ := tailInsertCLM n w
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ := ∂_{v} F
  have hv0 : v 0 = 0 := by simp [v, tailInsertCLM_apply]
  have htail : Fin.tail v = w := by
    ext i
    simp [v, tailInsertCLM_apply]
  rw [(hasFDerivAt_intervalPiece F x).fderiv]
  let φ : ℝ → (Fin n → ℝ) →L[ℝ] ℂ := fun t =>
    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ) (Fin.cons t (Fin.tail x))).comp
      (tailInsertCLM n)
  calc
    (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).smulRight (F x)) +
        ((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n))) v
        = (((∫ t in (0 : ℝ)..(x 0), φ t).comp (tailCLM n)) v) := by
            simp [ContinuousLinearMap.smulRight_apply, hv0]
    _ = (∫ t in (0 : ℝ)..(x 0), φ t) w := by
          rw [ContinuousLinearMap.comp_apply]
          simpa [tailCLM_apply] using congrArg (fun u => (∫ t in (0 : ℝ)..(x 0), φ t) u) htail
    _ = intervalPiece dF x := by
          rw [ContinuousLinearMap.intervalIntegral_apply]
          · simp [intervalPiece, dF, v, φ, SchwartzMap.lineDerivOp_apply_eq_fderiv,
              tailInsertCLM_apply]
          ·
            have hpath : Continuous fun t : ℝ => (Fin.cons t (Fin.tail x) : Fin (n + 1) → ℝ) := by
              classical
              refine continuous_pi ?_
              intro j
              refine Fin.cases ?_ ?_ j
              · simpa using (continuous_id : Continuous fun t : ℝ => t)
              · intro i
                simpa using (continuous_const : Continuous fun _ : ℝ => Fin.tail x i)
            have hcont : Continuous φ := by
              exact (((F.smooth 1).continuous_fderiv one_ne_zero).comp hpath).clm_comp continuous_const
            exact hcont.intervalIntegrable _ _

theorem head_tail_decomposition_sliceIntegral {n : ℕ} (y : Fin (n + 1) → ℝ) :
    y = (y 0) • ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) +
      tailInsertCLM n (tailCLM n y) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [tailInsertCLM_apply]
  · intro i
    simp [tailInsertCLM_apply, tailCLM_apply]

/-- Evaluating the derivative of the fixed `(-∞, 0]` slice piece on an
arbitrary direction depends only on the tail component of that direction. -/
theorem fderiv_iicZeroSlice_comp_tail_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x y : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
      iicZeroSlice
        (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) (Fin.tail x) := by
  have hcomp :=
    (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
      ((tailCLM n).hasFDerivAt)
  have hsame :
      fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
        fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x
          (tailInsertCLM n (tailCLM n y)) := by
    simpa [Function.comp, ContinuousLinearMap.comp_apply, tailCLM_apply] using
      congrArg
        (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℂ => L y = L (tailInsertCLM n (tailCLM n y)))
        hcomp.fderiv
  rw [hsame]
  simpa using
    fderiv_iicZeroSlice_comp_tail_tailInsert_eq F x (tailCLM n y)

/-- The head-fiber antiderivative is smooth as an ordinary function. -/
theorem contDiff_headFiberAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (headFiberAntiderivRaw F) := by
  have hdecomp : headFiberAntiderivRaw F =
      fun v => intervalPiece F v + iicZeroSlice F (Fin.tail v) := by
    ext v
    exact headFiberAntiderivRaw_eq_interval_add_iic F v
  rw [hdecomp]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (intervalPiece F) := contDiff_intervalPiece F
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail v)) := by
    exact (contDiff_iicZeroSlice F).comp (tailCLM n).contDiff
  exact h1.add h2

/-- The raw head-fiber antiderivative has the expected head-plus-tail derivative
formula: the head component gives the FTC term `F`, while the tail component is
again a head-fiber antiderivative of the corresponding line derivative of `F`. -/
theorem fderiv_headFiberAntiderivRaw_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (x y : Fin (n + 1) → ℝ) :
    fderiv ℝ (headFiberAntiderivRaw F) x y =
      (y 0 : ℝ) • F x +
        headFiberAntiderivRaw
          (∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F) x := by
  let dF : SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    ∂_{(tailInsertCLM n (tailCLM n y) : Fin (n + 1) → ℝ)} F
  have hdecomp :
      headFiberAntiderivRaw F =
        fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z) := by
    funext z
    exact headFiberAntiderivRaw_eq_interval_add_iic F z
  have hsum :=
    (hasFDerivAt_intervalPiece F x).add
      ((hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
        ((tailCLM n).hasFDerivAt))
  calc
    fderiv ℝ (headFiberAntiderivRaw F) x y
        = fderiv ℝ (fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z)) x y := by
            rw [hdecomp]
    _ = (y 0 : ℝ) • F x + intervalPiece dF x + iicZeroSlice dF (Fin.tail x) := by
            have hfun :
                (fun z : Fin (n + 1) → ℝ => intervalPiece F z + iicZeroSlice F (Fin.tail z)) =
                  (intervalPiece F) + (iicZeroSlice F ∘ Fin.tail) := rfl
            rw [hfun]
            have hsum_eval :
                (fderiv ℝ ((intervalPiece F) + (iicZeroSlice F ∘ Fin.tail)) x) y =
                  (y 0 : ℝ) • F x +
                    (((∫ t in (0 : ℝ)..(x 0),
                        (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                          (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y)) +
                      (∫ t in Set.Iic (0 : ℝ),
                        (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                          (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y)) := by
              simpa [Function.comp, add_assoc] using
                congrArg (fun L : (Fin (n + 1) → ℝ) →L[ℝ] ℂ => L y) hsum.fderiv
            have htail_eval :
                (((∫ t in (0 : ℝ)..(x 0),
                    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                      (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y)) +
                  (∫ t in Set.Iic (0 : ℝ),
                    (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                      (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y)) =
                  intervalPiece dF x + iicZeroSlice dF (Fin.tail x) := by
              have hinterval :
                  (∫ t in (0 : ℝ)..(x 0),
                      (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                        (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y) =
                    intervalPiece dF x := by
                have hraw := fderiv_intervalPiece_tailInsert_eq F x (tailCLM n y)
                rw [(hasFDerivAt_intervalPiece F x).fderiv] at hraw
                simpa [dF, ContinuousLinearMap.smulRight_apply,
                  ContinuousLinearMap.comp_apply, tailCLM_apply, tailInsertCLM_apply] using hraw
              have hiic :
                  (∫ t in Set.Iic (0 : ℝ),
                      (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                        (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                    (Fin.tail y) =
                    iicZeroSlice dF (Fin.tail x) := by
                have hcompTail :=
                  (hasFDerivAt_iicZeroSlice F (Fin.tail x)).comp x
                    ((tailCLM n).hasFDerivAt)
                have hexpl :
                    fderiv ℝ (fun z : Fin (n + 1) → ℝ => iicZeroSlice F (Fin.tail z)) x y =
                      (∫ t in Set.Iic (0 : ℝ),
                          (fderiv ℝ (F : (Fin (n + 1) → ℝ) → ℂ)
                            (Fin.cons t (Fin.tail x))).comp (tailInsertCLM n))
                        (Fin.tail y) := by
                  change (fderiv ℝ (iicZeroSlice F ∘ Fin.tail) x) y = _
                  rw [hcompTail.fderiv, ContinuousLinearMap.comp_apply, tailCLM_apply]
                  rfl
                exact hexpl.symm.trans (fderiv_iicZeroSlice_comp_tail_apply F x y)
              rw [hinterval, hiic]
            exact hsum_eval.trans <|
              by simpa [add_assoc] using
                congrArg (fun z : ℂ => (y 0 : ℝ) • F x + z) htail_eval
    _ = (y 0 : ℝ) • F x + headFiberAntiderivRaw dF x := by
            simpa [intervalPiece, iicZeroSlice, add_assoc] using
              congrArg (fun z : ℂ => (y 0 : ℝ) • F x + z)
                (headFiberAntiderivRaw_eq_interval_add_iic dF x).symm

/-- The tail representation: the zero-slice antiderivative can also be written
as an integral over the complementary upper tail. -/
theorem headFiberAntiderivRaw_eq_neg_ioi {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (v : Fin (n + 1) → ℝ) :
    headFiberAntiderivRaw F v = -(∫ t in Set.Ioi (v 0), F (Fin.cons t (Fin.tail v))) := by
  set y := Fin.tail v
  rw [headFiberAntiderivRaw]
  have hf_int := integrable_sliceSection F y
  have hsplit :
      ∫ t in Set.Iic (v 0), F (Fin.cons t y) =
        (∫ t : ℝ, F (Fin.cons t y)) - ∫ t in Set.Ioi (v 0), F (Fin.cons t y) := by
    have h := integral_add_compl (s := Set.Iic (v 0)) measurableSet_Iic hf_int
    rw [show (Set.Iic (v 0))ᶜ = Set.Ioi (v 0) by ext t; simp] at h
    linear_combination h
  rw [hsplit, hzero y, zero_sub]

/-- Zeroth-order decay for the raw head-fiber antiderivative. -/
theorem exists_norm_pow_mul_headFiberAntiderivRaw_le {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (k : ℕ) :
    ∃ C : ℝ, ∀ v : Fin (n + 1) → ℝ,
      ‖v‖ ^ k * ‖headFiberAntiderivRaw F v‖ ≤ C := by
  let S : ℝ := ((Finset.Iic (k + 2, 0)).sup
    (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)) F
  let M : ℝ := (2 : ℝ) ^ (k + 2) * S
  let C : ℝ := ∫ t : ℝ, M * (1 + t ^ 2)⁻¹
  refine ⟨C, ?_⟩
  intro v
  set y := Fin.tail v
  let zfun : ℝ → Fin (n + 1) → ℝ := fun t => Fin.cons t y
  have hmajor_point :
      ∀ t : ℝ, ‖zfun t‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
    intro t
    let z : Fin (n + 1) → ℝ := zfun t
    have hseminorm :
        (1 + ‖z‖) ^ (k + 2) * ‖F z‖ ≤ M := by
      simpa [M, S, z] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℝ) (m := (k + 2, 0)) (k := k + 2) (n := 0)
          le_rfl le_rfl F z)
    have hmain :
        ‖z‖ ^ k * ‖F z‖ ≤ M / (1 + ‖z‖) ^ (2 : ℕ) := by
      have hpow : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := by
        have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg _
        have hz_le : ‖z‖ ≤ 1 + ‖z‖ := by linarith
        exact pow_le_pow_left₀ hz_nonneg hz_le k
      have hden_pos : 0 < (1 + ‖z‖) ^ (2 : ℕ) := by positivity
      refine (le_div_iff₀ hden_pos).2 ?_
      calc
        (‖z‖ ^ k * ‖F z‖) * (1 + ‖z‖) ^ (2 : ℕ)
            = (‖z‖ ^ k * (1 + ‖z‖) ^ (2 : ℕ)) * ‖F z‖ := by ring
        _ ≤ ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ (2 : ℕ)) * ‖F z‖ := by
              gcongr
        _ = (1 + ‖z‖) ^ (k + 2) * ‖F z‖ := by
              rw [← pow_add]
        _ ≤ M := hseminorm
    have hhead : ‖t‖ ≤ ‖z‖ := by
      simpa [z] using (norm_le_pi_norm z 0)
    have hsq : 1 + t ^ 2 ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
      calc
        1 + t ^ 2 = 1 + ‖t‖ ^ 2 := by
              rw [Real.norm_eq_abs, sq_abs]
        _ ≤ 1 + 2 * ‖z‖ + ‖z‖ ^ 2 := by
              nlinarith [norm_nonneg t, hhead]
        _ = (1 + ‖z‖) ^ (2 : ℕ) := by ring
    have hsq_inv : ((1 + ‖z‖) ^ (2 : ℕ))⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
      have hpos : 0 < 1 + t ^ 2 := by positivity
      simpa [one_div] using (one_div_le_one_div_of_le hpos hsq)
    calc
      ‖zfun t‖ ^ k * ‖F (zfun t)‖ = ‖z‖ ^ k * ‖F z‖ := by rfl
      _ ≤ M * (((1 + ‖z‖) ^ (2 : ℕ))⁻¹) := by
            simpa [one_div, div_eq_mul_inv] using hmain
      _ ≤ M * (1 + t ^ 2)⁻¹ := by
            gcongr
  have hmajor_integrable :
      Integrable (fun t : ℝ => M * (1 + t ^ 2)⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      integrable_inv_one_add_sq.const_mul M
  have hmajor_nonneg : ∀ t : ℝ, 0 ≤ M * (1 + t ^ 2)⁻¹ := by
    intro t
    positivity
  by_cases hv0_nonneg : 0 ≤ v 0
  · have hrepr := headFiberAntiderivRaw_eq_neg_ioi F hzero v
    have hnorm_int : IntegrableOn (fun t : ℝ => ‖F (zfun t)‖) (Set.Ioi (v 0)) volume := by
      simpa [y, zfun] using (integrable_sliceSection F y).norm.integrableOn
    have hleft_int :
        IntegrableOn (fun t : ℝ => ‖v‖ ^ k * ‖F (zfun t)‖) (Set.Ioi (v 0)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm_int.const_mul (‖v‖ ^ k)
    have hright_int :
        IntegrableOn (fun t : ℝ => M * (1 + t ^ 2)⁻¹) (Set.Ioi (v 0)) volume := by
      exact hmajor_integrable.integrableOn
    have hdom :
        ∀ t ∈ Set.Ioi (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      intro t ht
      have ht0 : 0 ≤ t := le_trans hv0_nonneg (le_of_lt ht)
      have hcoord : ∀ j : Fin (n + 1), ‖v j‖ ≤ ‖zfun t‖ := by
        intro j
        refine Fin.cases ?_ ?_ j
        · calc
            ‖v 0‖ = v 0 := by simp [Real.norm_of_nonneg hv0_nonneg]
            _ ≤ t := le_of_lt ht
            _ = ‖t‖ := by simp [Real.norm_of_nonneg ht0]
            _ ≤ ‖zfun t‖ := by simpa [zfun] using (norm_le_pi_norm (zfun t) 0)
        · intro i
          calc
            ‖v i.succ‖ = ‖y i‖ := by
              change ‖v i.succ‖ = ‖v i.succ‖
              rfl
            _ ≤ ‖y‖ := by simpa using (norm_le_pi_norm y i)
            _ = ‖tailCLM n (zfun t)‖ := by simp [tailCLM_apply, zfun, y]
            _ ≤ ‖tailCLM n‖ * ‖zfun t‖ := by
                exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖zfun t‖ := by
                gcongr
                exact tailCLM_opNorm_le n
            _ = ‖zfun t‖ := by ring
      have hv_le : ‖v‖ ≤ ‖zfun t‖ := by
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hcoord
      have hpow : ‖v‖ ^ k ≤ ‖zfun t‖ ^ k := by
        exact pow_le_pow_left₀ (norm_nonneg _) hv_le k
      calc
        ‖v‖ ^ k * ‖F (zfun t)‖ ≤ ‖zfun t‖ ^ k * ‖F (zfun t)‖ := by
              gcongr
        _ ≤ M * (1 + t ^ 2)⁻¹ := hmajor_point t
    calc
      ‖v‖ ^ k * ‖headFiberAntiderivRaw F v‖
          = ‖v‖ ^ k * ‖∫ t in Set.Ioi (v 0), F (zfun t)‖ := by
              rw [hrepr, norm_neg]
      _ ≤ ‖v‖ ^ k * ∫ t in Set.Ioi (v 0), ‖F (zfun t)‖ := by
            gcongr
            simpa using
              (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (v 0)))
                (f := fun t : ℝ => F (zfun t)))
      _ = ∫ t in Set.Ioi (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ := by
            rw [← integral_const_mul]
      _ ≤ ∫ t in Set.Ioi (v 0), M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_mono_on hleft_int hright_int measurableSet_Ioi hdom
      _ ≤ ∫ t : ℝ, M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_le_integral
              (hfi := hmajor_integrable)
              (hf := Filter.Eventually.of_forall hmajor_nonneg)
      _ = C := by rfl
  · have hv0_nonpos : v 0 ≤ 0 := le_of_not_ge hv0_nonneg
    have hnorm_int : IntegrableOn (fun t : ℝ => ‖F (zfun t)‖) (Set.Iic (v 0)) volume := by
      simpa [y, zfun] using (integrable_sliceSection F y).norm.integrableOn
    have hleft_int :
        IntegrableOn (fun t : ℝ => ‖v‖ ^ k * ‖F (zfun t)‖) (Set.Iic (v 0)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnorm_int.const_mul (‖v‖ ^ k)
    have hright_int :
        IntegrableOn (fun t : ℝ => M * (1 + t ^ 2)⁻¹) (Set.Iic (v 0)) volume := by
      exact hmajor_integrable.integrableOn
    have hdom :
        ∀ t ∈ Set.Iic (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ ≤ M * (1 + t ^ 2)⁻¹ := by
      intro t ht
      have htv : t ≤ v 0 := by simpa using ht
      have ht_nonpos : t ≤ 0 := le_trans htv hv0_nonpos
      have hcoord : ∀ j : Fin (n + 1), ‖v j‖ ≤ ‖zfun t‖ := by
        intro j
        refine Fin.cases ?_ ?_ j
        · calc
            ‖v 0‖ = -v 0 := by simp [Real.norm_of_nonpos hv0_nonpos]
            _ ≤ -t := by linarith
            _ = ‖t‖ := by simp [Real.norm_of_nonpos ht_nonpos]
            _ ≤ ‖zfun t‖ := by simpa [zfun] using (norm_le_pi_norm (zfun t) 0)
        · intro i
          calc
            ‖v i.succ‖ = ‖y i‖ := by
              change ‖v i.succ‖ = ‖v i.succ‖
              rfl
            _ ≤ ‖y‖ := by simpa using (norm_le_pi_norm y i)
            _ = ‖tailCLM n (zfun t)‖ := by simp [tailCLM_apply, zfun, y]
            _ ≤ ‖tailCLM n‖ * ‖zfun t‖ := by
                exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖zfun t‖ := by
                gcongr
                exact tailCLM_opNorm_le n
            _ = ‖zfun t‖ := by ring
      have hv_le : ‖v‖ ≤ ‖zfun t‖ := by
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hcoord
      have hpow : ‖v‖ ^ k ≤ ‖zfun t‖ ^ k := by
        exact pow_le_pow_left₀ (norm_nonneg _) hv_le k
      calc
        ‖v‖ ^ k * ‖F (zfun t)‖ ≤ ‖zfun t‖ ^ k * ‖F (zfun t)‖ := by
              gcongr
        _ ≤ M * (1 + t ^ 2)⁻¹ := hmajor_point t
    calc
      ‖v‖ ^ k * ‖headFiberAntiderivRaw F v‖
          = ‖v‖ ^ k * ‖∫ t in Set.Iic (v 0), F (zfun t)‖ := by
              simp [headFiberAntiderivRaw, y, zfun]
      _ ≤ ‖v‖ ^ k * ∫ t in Set.Iic (v 0), ‖F (zfun t)‖ := by
            gcongr
            simpa using
              (norm_integral_le_integral_norm (μ := volume.restrict (Set.Iic (v 0)))
                (f := fun t : ℝ => F (zfun t)))
      _ = ∫ t in Set.Iic (v 0), ‖v‖ ^ k * ‖F (zfun t)‖ := by
            rw [← integral_const_mul]
      _ ≤ ∫ t in Set.Iic (v 0), M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_mono_on hleft_int hright_int measurableSet_Iic hdom
      _ ≤ ∫ t : ℝ, M * (1 + t ^ 2)⁻¹ := by
            exact setIntegral_le_integral
              (hfi := hmajor_integrable)
              (hf := Filter.Eventually.of_forall hmajor_nonneg)
      _ = C := by rfl

/-- Linearity of `headFiberAntiderivRaw` in the Schwartz argument. -/
theorem headFiberAntiderivRaw_add {n : ℕ}
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    headFiberAntiderivRaw (F + G) v =
      headFiberAntiderivRaw F v + headFiberAntiderivRaw G v := by
  simp [headFiberAntiderivRaw, SchwartzMap.add_apply]
  rw [← MeasureTheory.integral_add
    (integrable_sliceSection F (Fin.tail v)).integrableOn
    (integrable_sliceSection G (Fin.tail v)).integrableOn]

/-- Scalar linearity of `headFiberAntiderivRaw`. -/
theorem headFiberAntiderivRaw_smul {n : ℕ}
    (c : ℝ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (v : Fin (n + 1) → ℝ) :
    headFiberAntiderivRaw (c • F) v =
      c • headFiberAntiderivRaw F v := by
  simp only [headFiberAntiderivRaw, SchwartzMap.smul_apply]
  exact MeasureTheory.integral_smul c _

/-- Linearity of `headFiberAntiderivRaw` over finite sums. -/
theorem headFiberAntiderivRaw_finset_sum {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (v : Fin (n + 1) → ℝ) :
    headFiberAntiderivRaw (s.sum f) v =
      s.sum (fun i => headFiberAntiderivRaw (f i) v) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    simp [headFiberAntiderivRaw, SchwartzMap.zero_apply, MeasureTheory.integral_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [headFiberAntiderivRaw_add, ih]

/-- Basis decomposition of the Fréchet derivative of `headFiberAntiderivRaw`. -/
theorem fderiv_headFiberAntiderivRaw_eq_sum {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (headFiberAntiderivRaw F) x =
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0) (F x) +
      Finset.univ.sum (fun i : Fin n =>
        ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) i.succ)
          (headFiberAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F) x)) := by
  ext h
  rw [fderiv_headFiberAntiderivRaw_apply F x h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  congr 1
  have htail : tailCLM n h = Finset.univ.sum
      (fun i : Fin n => (h i.succ : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    ext j; simp [tailCLM_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
  have hdir : tailInsertCLM n (tailCLM n h) =
      Finset.univ.sum (fun i : Fin n =>
        (h i.succ : ℝ) • (tailInsertCLM n (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)) := by
    rw [htail]; simp [map_sum]
  have hext : ∂_{(tailInsertCLM n (tailCLM n h) : Fin (n + 1) → ℝ)} F =
      Finset.univ.sum (fun i : Fin n =>
        (h i.succ) • ∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) := by
    ext v
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hdir, map_sum]
    simp only [ContinuousLinearMap.map_smul]
    have hsum_coe : ∀ (s : Finset (Fin n))
        (f : Fin n → SchwartzMap (Fin (n + 1) → ℝ) ℂ) (w : Fin (n + 1) → ℝ),
        (s.sum f) w = s.sum (fun i => (f i) w) := by
      intro s f w
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih => simp [Finset.sum_insert ha, SchwartzMap.add_apply, ih]
    rw [hsum_coe]
    simp only [SchwartzMap.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hclm_sum : ∀ (s : Finset (Fin n))
      (f : Fin n → (Fin (n + 1) → ℝ) →L[ℝ] ℂ) (w : Fin (n + 1) → ℝ),
      (s.sum f) w = s.sum (fun i => (f i) w) := by
    intro s f w
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      simp [Finset.sum_insert ha, ContinuousLinearMap.add_apply, ih]
  rw [hclm_sum]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  rw [hext, headFiberAntiderivRaw_finset_sum, show Finset.univ.sum
    (fun i : Fin n => headFiberAntiderivRaw ((h i.succ) • ∂_{(tailInsertCLM n
      (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x) = Finset.univ.sum
    (fun i : Fin n => (h i.succ) • headFiberAntiderivRaw (∂_{(tailInsertCLM n
      (Pi.single i (1 : ℝ)) : Fin (n + 1) → ℝ)} F) x)
    from Finset.sum_congr rfl (fun i _ => headFiberAntiderivRaw_smul _ _ _)]
  rfl

/-- Full Schwartz decay for the raw head-fiber antiderivative under the
zero-slice condition. -/
theorem decay_headFiberAntiderivRaw {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (k p : ℕ) :
    ∃ C : ℝ, ∀ v : Fin (n + 1) → ℝ,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ p (headFiberAntiderivRaw F) v‖ ≤ C := by
  induction p generalizing n F with
  | zero =>
      obtain ⟨C, hC⟩ := exists_norm_pow_mul_headFiberAntiderivRaw_le F hzero k
      exact ⟨C, fun v => by rw [norm_iteratedFDeriv_zero]; exact hC v⟩
  | succ p ihp =>
      obtain ⟨C_head, hC_head⟩ := F.decay' k p
      have hIH : ∀ i : Fin n, ∃ C_i : ℝ, ∀ v : Fin (n + 1) → ℝ,
          ‖v‖ ^ k * ‖iteratedFDeriv ℝ p
            (headFiberAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F)) v‖ ≤ C_i :=
        fun i => ihp _ (zeroSlice_lineDerivOp_tailInsert F hzero (Pi.single i 1))
      choose C_tail hC_tail using hIH
      let L₀ : ℂ →L[ℝ] ((Fin (n + 1) → ℝ) →L[ℝ] ℂ) :=
        ContinuousLinearMap.smulRightL ℝ (Fin (n + 1) → ℝ) ℂ
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0)
      let Lᵢ : Fin n → (ℂ →L[ℝ] ((Fin (n + 1) → ℝ) →L[ℝ] ℂ)) := fun i =>
        ContinuousLinearMap.smulRightL ℝ (Fin (n + 1) → ℝ) ℂ
          (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) i.succ)
      let fᵢ : Fin n → ((Fin (n + 1) → ℝ) → ℂ) := fun i =>
        headFiberAntiderivRaw (∂_{(tailInsertCLM n (Pi.single i (1 : ℝ)))} F)
      have hF_cd : ContDiff ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) := F.smooth p
      have hfᵢ_cd : ∀ i : Fin n, ContDiff ℝ p (fᵢ i) := fun i => by
        exact (contDiff_infty.mp (contDiff_headFiberAntiderivRaw _)) p
      have hfderiv_fun : fderiv ℝ (headFiberAntiderivRaw F) =
          (fun v => L₀ (F v)) + (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) := by
        funext v; exact fderiv_headFiberAntiderivRaw_eq_sum F v
      have hA_cd : ContDiff ℝ p (fun v => L₀ (F v)) := L₀.contDiff.comp hF_cd
      have hB_cd : ContDiff ℝ p
          (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) :=
        ContDiff.sum (fun i _ => (Lᵢ i).contDiff.comp (hfᵢ_cd i))
      have hstep4_head : ∀ v, ‖iteratedFDeriv ℝ p (fun v => L₀ (F v)) v‖ ≤
          ‖L₀‖ * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖ :=
        fun v => L₀.norm_iteratedFDeriv_comp_left hF_cd.contDiffAt le_rfl
      have hstep4_tail : ∀ v,
          ‖iteratedFDeriv ℝ p (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v‖ ≤
          Finset.univ.sum (fun i => ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖) := by
        intro v
        set_option synthInstance.maxHeartbeats 40000 in
        have hsum_eq : iteratedFDeriv ℝ p
            (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v =
            Finset.univ.sum (fun i =>
              iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v) := by
          have key := congr_fun (iteratedFDeriv_sum (𝕜 := ℝ) (i := p)
            (f := fun (j : Fin n) (v : Fin (n + 1) → ℝ) => Lᵢ j (fᵢ j v))
            (u := Finset.univ)
            (fun j _ => (Lᵢ j).contDiff.comp (hfᵢ_cd j))) v
          rw [show (fun v => ∑ i : Fin n, (Lᵢ i) (fᵢ i v)) =
            (fun x => ∑ j : Fin n, (fun j v => Lᵢ j (fᵢ j v)) j x) from rfl]
          rw [key]
          simp only [Finset.sum_apply]
        rw [hsum_eq]
        calc ‖Finset.univ.sum (fun i =>
                iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v)‖
            ≤ Finset.univ.sum (fun i =>
                ‖iteratedFDeriv ℝ p (fun v => Lᵢ i (fᵢ i v)) v‖) := norm_sum_le _ _
          _ ≤ Finset.univ.sum (fun i =>
                ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖) :=
              Finset.sum_le_sum (fun i _ =>
                (Lᵢ i).norm_iteratedFDeriv_comp_left (hfᵢ_cd i).contDiffAt le_rfl)
      let C_total := ‖L₀‖ * C_head + Finset.univ.sum (fun i => ‖Lᵢ i‖ * C_tail i)
      refine ⟨C_total, fun v => ?_⟩
      calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ (p + 1) (headFiberAntiderivRaw F) v‖
          = ‖v‖ ^ k * ‖iteratedFDeriv ℝ p (fderiv ℝ (headFiberAntiderivRaw F)) v‖ := by
            rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
        _ = ‖v‖ ^ k * ‖iteratedFDeriv ℝ p ((fun v => L₀ (F v)) +
              (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v)))) v‖ := by
            congr 2
            exact congr_fun (congr_arg (iteratedFDeriv ℝ p) hfderiv_fun) v
        _ ≤ ‖v‖ ^ k * (‖iteratedFDeriv ℝ p (fun v => L₀ (F v)) v‖ +
              ‖iteratedFDeriv ℝ p (fun v => Finset.univ.sum (fun i => Lᵢ i (fᵢ i v))) v‖) := by
            gcongr
            rw [iteratedFDeriv_add hA_cd hB_cd]
            exact norm_add_le _ _
        _ ≤ ‖v‖ ^ k * (‖L₀‖ * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖ +
              Finset.univ.sum (fun i => ‖Lᵢ i‖ * ‖iteratedFDeriv ℝ p (fᵢ i) v‖)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hstep4_head v) (hstep4_tail v)) (by positivity)
        _ = ‖L₀‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ p (F : (Fin (n + 1) → ℝ) → ℂ) v‖) +
              Finset.univ.sum (fun i =>
                ‖Lᵢ i‖ * (‖v‖ ^ k * ‖iteratedFDeriv ℝ p (fᵢ i) v‖)) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ ‖L₀‖ * C_head + Finset.univ.sum (fun i => ‖Lᵢ i‖ * C_tail i) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hC_head v) (norm_nonneg L₀)
            · exact Finset.sum_le_sum (fun i _ =>
                mul_le_mul_of_nonneg_left (hC_tail i v) (norm_nonneg (Lᵢ i)))

/-- The Schwartz head-fiber antiderivative obtained from the raw one under the
zero-slice condition. -/
noncomputable def headFiberAntideriv {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
  SchwartzMap.mk (headFiberAntiderivRaw F)
    (contDiff_headFiberAntiderivRaw F)
    (decay_headFiberAntiderivRaw F hzero)

/-- Differentiating the Schwartz antiderivative in the head direction recovers
the original Schwartz function. -/
theorem lineDeriv_headFiberAntideriv {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0)
    (v : Fin (n + 1) → ℝ) :
    lineDeriv ℝ (⇑(headFiberAntideriv F hzero)) v (Pi.single 0 1) = F v :=
  lineDeriv_headFiberAntiderivRaw F v

/-- Operator-form version of the head-fiber antiderivative identity. -/
theorem lineDerivOp_headFiberAntideriv {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0) :
    LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ)
      (headFiberAntideriv F hzero) = F := by
  ext v
  simpa [SchwartzMap.lineDerivOp_apply] using lineDeriv_headFiberAntideriv F hzero v

/-- Existence form consumed by one-coordinate head-block descent. -/
theorem exists_headFiberAntideriv_of_integral_eq_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hzero : ∀ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) = 0) :
    ∃ H : SchwartzMap (Fin (n + 1) → ℝ) ℂ,
      LineDeriv.lineDerivOp ((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ) H = F := by
  exact ⟨headFiberAntideriv F hzero, lineDerivOp_headFiberAntideriv F hzero⟩

end SCV
