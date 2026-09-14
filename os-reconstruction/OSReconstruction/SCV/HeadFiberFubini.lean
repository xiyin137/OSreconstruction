/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.HeadBlockDescent
import OSReconstruction.SCV.LocalProductDescent


















noncomputable section

open Complex MeasureTheory
open scoped Classical SchwartzMap Topology

namespace SCV

noncomputable def headTailProductSchwartzCLM (n : ℕ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ]
      SchwartzMap (ℝ × (Fin n → ℝ)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ))

@[simp]
theorem headTailProductSchwartzCLM_apply
    {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (t : ℝ)
    (y : Fin n → ℝ) :
    headTailProductSchwartzCLM n F (t, y) = F (Fin.cons t y) := by
  rfl

private theorem headPartialEval_seminorm_decay_one_bound
    {n : ℕ}
    (k l : ℕ) :
    let N := (volume : Measure ℝ).integrablePower
    let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
    let C : ℝ := (2 : ℝ) ^ N * 2
    0 ≤ C ∧
      ∀ (A : SchwartzMap (ℝ × (Fin n → ℝ)) ℂ)
        (t : ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₁ A t) ≤
          C * (1 + ‖t‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              (ℝ × (Fin n → ℝ)) ℂ) A := by
  let B := Fin n → ℝ
  let N := (volume : Measure ℝ).integrablePower
  let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
  let C : ℝ := (2 : ℝ) ^ N * 2
  change 0 ≤ C ∧
      ∀ (A : SchwartzMap (ℝ × B) ℂ) (t : ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₁ A t) ≤
          C * (1 + ‖t‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ (ℝ × B) ℂ) A
  refine ⟨by positivity, ?_⟩
  intro A t
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ (ℝ × B) ℂ) A
  let r : ℝ := (1 + ‖t‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have hC₁_le : SchwartzMap.seminorm ℂ k l A ≤ S := by
    have hmem : ((k, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (ℝ × B) ℂ ((k, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (ℝ × B) ℂ) hmem) A)
  have hC₂_le : SchwartzMap.seminorm ℂ (k + N) l A ≤ S := by
    have hmem : ((k + N, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (ℝ × B) ℂ ((k + N, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (ℝ × B) ℂ) hmem) A)
  apply SchwartzMap.seminorm_le_bound ℂ k l _
    (mul_nonneg (mul_nonneg (by positivity) hr_nonneg) hS_nonneg)
  intro y
  let D : ℝ :=
    ‖iteratedFDeriv ℝ l (fun y' => (schwartzPartialEval₁ A t) y') y‖
  let E : ℝ := ‖iteratedFDeriv ℝ l (⇑A) (t, y)‖
  have hD_nonneg : 0 ≤ D := norm_nonneg _
  have hE_nonneg : 0 ≤ E := norm_nonneg _
  have hderiv : D ≤ E := by
    simpa [D, E, schwartzPartialEval₁_apply] using
      norm_iteratedFDeriv_partialEval₁_le A t l y
  have hy_norm : ‖y‖ ≤ ‖(t, y)‖ := by
    rw [Prod.norm_def]
    exact le_max_right ‖t‖ ‖y‖
  have ht_norm : ‖t‖ ≤ ‖(t, y)‖ := by
    rw [Prod.norm_def]
    exact le_max_left ‖t‖ ‖y‖
  have h₁ : ‖y‖ ^ k * D ≤ SchwartzMap.seminorm ℂ k l A := by
    calc
      ‖y‖ ^ k * D ≤ ‖y‖ ^ k * E :=
        mul_le_mul_of_nonneg_left hderiv (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖(t, y)‖ ^ k * E := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hy_norm _) hE_nonneg
      _ ≤ SchwartzMap.seminorm ℂ k l A :=
        SchwartzMap.le_seminorm ℂ k l A (t, y)
  have hpow_prod : ‖t‖ ^ N * ‖y‖ ^ k ≤ ‖(t, y)‖ ^ (k + N) := by
    have ht_pow : ‖t‖ ^ N ≤ ‖(t, y)‖ ^ N :=
      pow_le_pow_left₀ (norm_nonneg _) ht_norm _
    have hy_pow : ‖y‖ ^ k ≤ ‖(t, y)‖ ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hy_norm _
    calc
      ‖t‖ ^ N * ‖y‖ ^ k ≤ ‖(t, y)‖ ^ N * ‖(t, y)‖ ^ k :=
        mul_le_mul ht_pow hy_pow (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg (norm_nonneg _) _)
      _ = ‖(t, y)‖ ^ (N + k) := by rw [pow_add]
      _ = ‖(t, y)‖ ^ (k + N) := by rw [add_comm]
  have h₂ : ‖t‖ ^ N * (‖y‖ ^ k * D) ≤
      SchwartzMap.seminorm ℂ (k + N) l A := by
    calc
      ‖t‖ ^ N * (‖y‖ ^ k * D) =
          (‖t‖ ^ N * ‖y‖ ^ k) * D := by ring
      _ ≤ ‖(t, y)‖ ^ (k + N) * E :=
        mul_le_mul hpow_prod hderiv hD_nonneg
          (pow_nonneg (norm_nonneg _) _)
      _ ≤ SchwartzMap.seminorm ℂ (k + N) l A :=
        SchwartzMap.le_seminorm ℂ (k + N) l A (t, y)
  have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := N)
    (x := ‖t‖) (f := ‖y‖ ^ k * D)
    (C₁ := SchwartzMap.seminorm ℂ k l A)
    (C₂ := SchwartzMap.seminorm ℂ (k + N) l A)
    (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) hD_nonneg)
    h₁ (by simpa using h₂)
  have hsum_le : SchwartzMap.seminorm ℂ k l A +
      SchwartzMap.seminorm ℂ (k + N) l A ≤ 2 * S := by
    linarith
  calc
    ‖y‖ ^ k *
        ‖iteratedFDeriv ℝ l
          (fun y' => (schwartzPartialEval₁ A t) y') y‖
        = ‖y‖ ^ k * D := rfl
    _ ≤ (2 : ℝ) ^ N *
          (SchwartzMap.seminorm ℂ k l A +
            SchwartzMap.seminorm ℂ (k + N) l A) * r := by
      simpa [r] using hmain
    _ ≤ (2 : ℝ) ^ N * (2 * S) * r := by
      gcongr
    _ = C * r * S := by
      simp [C]
      ring

/-- Finite-family seminorm decay for fixed-head partial evaluation. -/
theorem headPartialEval_finsetSeminorm_decay
    {n : ℕ}
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap (ℝ × (Fin n → ℝ)) ℂ)
        (t : ℝ),
        s0.sup (schwartzSeminormFamily ℂ
            (Fin n → ℝ) ℂ)
            (schwartzPartialEval₁ A t) ≤
          C * (1 + ‖t‖) ^
              (-((volume : Measure ℝ).integrablePower : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              (ℝ × (Fin n → ℝ)) ℂ) A := by
  let N := (volume : Measure ℝ).integrablePower
  let source : ℕ × ℕ → Finset (ℕ × ℕ) :=
    fun i => {i, (i.1 + N, i.2)}
  let s : Finset (ℕ × ℕ) := s0.biUnion source
  let C0 : ℝ := (2 : ℝ) ^ N * 2
  let C : ℝ := ∑ i ∈ s0, C0
  refine ⟨s, C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => by positivity
  intro A t
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ
    (ℝ × (Fin n → ℝ)) ℂ) A
  let r : ℝ := (1 + ‖t‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have htarget_nonneg : 0 ≤ C * r * S :=
    mul_nonneg (mul_nonneg
      (Finset.sum_nonneg fun _ _ => by positivity) hr_nonneg) hS_nonneg
  apply Seminorm.finset_sup_apply_le
  · simpa [N, s, C, S, r, mul_assoc] using htarget_nonneg
  intro i hi
  rcases i with ⟨k, l⟩
  let sOne : Finset (ℕ × ℕ) := source (k, l)
  let SOne : ℝ := sOne.sup (schwartzSeminormFamily ℂ
    (ℝ × (Fin n → ℝ)) ℂ) A
  have hOne :=
    (headPartialEval_seminorm_decay_one_bound (n := n) k l).2 A t
  have hSOne_le : SOne ≤ S := by
    apply Seminorm.finset_sup_apply_le
    · exact hS_nonneg
    intro j hj
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℂ
        (ℝ × (Fin n → ℝ)) ℂ)
      (s := s) (x := A)
      (by
        exact Finset.mem_biUnion.mpr ⟨(k, l), hi, hj⟩))
  have hC0_nonneg : 0 ≤ C0 := by positivity
  have hC0_le_C : C0 ≤ C := by
    simpa [C] using Finset.single_le_sum (fun _ _ => hC0_nonneg) hi
  calc
    (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ (k, l))
        (schwartzPartialEval₁ A t)
        ≤ C0 * r * SOne := by
      simpa [N, C0, sOne, SOne, source, r] using hOne
    _ ≤ C0 * r * S := by
      gcongr
    _ ≤ C * r * S := by
      gcongr

/-- After applying a continuous tail functional to fixed-head evaluations, the
head parameter is integrable. -/
theorem integrable_apply_headPartialEval
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (A : SchwartzMap (ℝ × (Fin n → ℝ)) ℂ) :
    Integrable (fun t : ℝ => L (schwartzPartialEval₁ A t)) := by
  let B := Fin n → ℝ
  let μ : Measure ℝ := volume
  obtain ⟨s0, C0, hC0, hLbound⟩ :=
    exists_schwartzFunctional_finsetSeminormBound (E := B) L
  obtain ⟨s, C, hC, hdecay⟩ :=
    headPartialEval_finsetSeminorm_decay (n := n) s0
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ (ℝ × B) ℂ) A
  let K : ℝ := C0 * C * S
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hK_nonneg : 0 ≤ K := mul_nonneg (mul_nonneg hC0 hC) hS_nonneg
  have htail : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) μ :=
    Measure.integrable_pow_neg_integrablePower μ
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => L (schwartzPartialEval₁ A t)) μ :=
    (L.continuous.comp
      (continuous_schwartzPartialEval₁ A)).aestronglyMeasurable
  refine Integrable.mono' (htail.mul_const K) hmeas
    (Filter.Eventually.of_forall ?_)
  intro t
  let r : ℝ := (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))
  have hr_nonneg : 0 ≤ r := by positivity
  have hpoint :
      ‖L (schwartzPartialEval₁ A t)‖ ≤ r * K := by
    calc
      ‖L (schwartzPartialEval₁ A t)‖
          ≤ C0 * s0.sup (schwartzSeminormFamily ℂ B ℂ)
              (schwartzPartialEval₁ A t) := hLbound _
      _ ≤ C0 * (C * r * S) := by
          gcongr
          simpa [B, μ, S, r] using hdecay A t
      _ = r * K := by
          ring
  have hrK_nonneg : 0 ≤ r * K := mul_nonneg hr_nonneg hK_nonneg
  simpa [r, Real.norm_eq_abs, abs_of_nonneg hrK_nonneg] using hpoint

/-- Uniform finite-seminorm bound for the scalar fixed-head integral. -/
theorem exists_bound_apply_headPartialEval_integral
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : SchwartzMap (ℝ × (Fin n → ℝ)) ℂ,
        ‖∫ t : ℝ, L (schwartzPartialEval₁ A t)‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ
            (ℝ × (Fin n → ℝ)) ℂ) A := by
  let B := Fin n → ℝ
  let μ : Measure ℝ := volume
  obtain ⟨s0, C0, hC0, hLbound⟩ :=
    exists_schwartzFunctional_finsetSeminormBound (E := B) L
  obtain ⟨s, C, hC, hdecay⟩ :=
    headPartialEval_finsetSeminorm_decay (n := n) s0
  let I : ℝ := ∫ t : ℝ,
    (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))
  refine ⟨s, C0 * C * I, ?_, ?_⟩
  · have htail_nonneg : 0 ≤ I :=
      integral_nonneg fun _ => by positivity
    exact mul_nonneg (mul_nonneg hC0 hC) htail_nonneg
  intro A
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ (ℝ × B) ℂ) A
  let K : ℝ := C0 * C * S
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have htail : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) μ :=
    Measure.integrable_pow_neg_integrablePower μ
  have hdom : Integrable
      (fun t : ℝ =>
        (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ)) * K) μ :=
    htail.mul_const K
  have hscalar_int := integrable_apply_headPartialEval L A
  have hpoint : ∀ t : ℝ,
      ‖L (schwartzPartialEval₁ A t)‖ ≤
        (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ)) * K := by
    intro t
    let r : ℝ := (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))
    calc
      ‖L (schwartzPartialEval₁ A t)‖
          ≤ C0 * s0.sup (schwartzSeminormFamily ℂ B ℂ)
              (schwartzPartialEval₁ A t) := hLbound _
      _ ≤ C0 * (C * r * S) := by
          gcongr
          simpa [B, μ, S, r] using hdecay A t
      _ = r * K := by
          ring
  calc
    ‖∫ t : ℝ, L (schwartzPartialEval₁ A t)‖
        ≤ ∫ t : ℝ, ‖L (schwartzPartialEval₁ A t)‖ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ,
          (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ)) * K :=
        integral_mono_ae hscalar_int.norm hdom
          (Filter.Eventually.of_forall hpoint)
    _ = (C0 * C * I) * S := by
        rw [integral_mul_const]
        ring

/-- Scalar integration of fixed-head partial evaluations as a continuous
functional on product-coordinate Schwartz space. -/
noncomputable def headPartialEvalScalarCLM
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    SchwartzMap (ℝ × (Fin n → ℝ)) ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
    (fun A => ∫ t : ℝ, L (schwartzPartialEval₁ A t))
    (fun A B => by
      have hA := integrable_apply_headPartialEval L A
      have hB := integrable_apply_headPartialEval L B
      have hsections :
          (fun t : ℝ => L (schwartzPartialEval₁ (A + B) t)) =
            fun t : ℝ =>
              L (schwartzPartialEval₁ A t) +
                L (schwartzPartialEval₁ B t) := by
        funext t
        have hpartial :
            schwartzPartialEval₁ (A + B) t =
              schwartzPartialEval₁ A t + schwartzPartialEval₁ B t := by
          ext y
          rfl
        rw [hpartial, map_add]
      change
        (∫ t : ℝ, L (schwartzPartialEval₁ (A + B) t)) =
          (∫ t : ℝ, L (schwartzPartialEval₁ A t)) +
            ∫ t : ℝ, L (schwartzPartialEval₁ B t)
      rw [hsections]
      exact integral_add hA hB)
    (fun c A => by
      have hsections :
          (fun t : ℝ => L (schwartzPartialEval₁ (c • A) t)) =
            fun t : ℝ => c * L (schwartzPartialEval₁ A t) := by
        funext t
        have hpartial :
            schwartzPartialEval₁ (c • A) t =
              c • schwartzPartialEval₁ A t := by
          ext y
          rfl
        rw [hpartial, map_smul]
        rfl
      change
        (∫ t : ℝ, L (schwartzPartialEval₁ (c • A) t)) =
          c * ∫ t : ℝ, L (schwartzPartialEval₁ A t)
      rw [hsections]
      exact integral_const_mul (μ := (volume : Measure ℝ)) c
        (fun t : ℝ => L (schwartzPartialEval₁ A t)))
    (exists_bound_apply_headPartialEval_integral L)

/-- Scalar integration of fixed-head sections in flat `Fin` coordinates. -/
noncomputable def headSliceScalarCLM
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  (headPartialEvalScalarCLM L).comp (headTailProductSchwartzCLM n)

@[simp]
theorem headSliceScalarCLM_apply
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    headSliceScalarCLM L F =
      ∫ t : ℝ,
        L (schwartzPartialEval₁ (headTailProductSchwartzCLM n F) t) := by
  rfl

theorem isHeadTranslationInvariant_headSliceScalarCLM
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    IsHeadTranslationInvariantSchwartzCLM (headSliceScalarCLM L) := by
  intro a
  ext F
  rw [ContinuousLinearMap.comp_apply]
  simp only [headSliceScalarCLM_apply]
  rw [← integral_add_right_eq_self
    (f := fun t : ℝ =>
      L (schwartzPartialEval₁ (headTailProductSchwartzCLM n F) t)) a]
  apply integral_congr_ae
  filter_upwards with t
  apply congrArg L
  ext y
  simp only [translateSchwartzCLM_apply, headTailProductSchwartzCLM_apply,
    schwartzPartialEval₁_apply, translateSchwartz_apply]
  congr 1
  ext j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro i
    simp

theorem headTranslationDescentCLM_headSliceScalarCLM
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    headTranslationDescentCLM
        (headSliceScalarCLM L) normedUnitBumpSchwartz =
      L := by
  ext g
  rw [headTranslationDescentCLM, ContinuousLinearMap.comp_apply]
  simp only [prependFieldCLMRight_apply, headSliceScalarCLM_apply]
  calc
    (∫ t : ℝ,
        L (schwartzPartialEval₁
          (headTailProductSchwartzCLM n
            (prependField normedUnitBumpSchwartz g)) t)) =
        ∫ t : ℝ, normedUnitBumpSchwartz t * L g := by
      apply integral_congr_ae
      filter_upwards with t
      have hsection :
          schwartzPartialEval₁
              (headTailProductSchwartzCLM n
                (prependField normedUnitBumpSchwartz g)) t =
            normedUnitBumpSchwartz t • g := by
        ext y
        rfl
      rw [hsection, map_smul]
      simp [smul_eq_mul]
    _ = (∫ t : ℝ, normedUnitBumpSchwartz t) * L g := by
      simpa using
        (integral_mul_const (L g)
          (fun t : ℝ => normedUnitBumpSchwartz t))
    _ = L g := by
      rw [integral_normedUnitBumpSchwartz]
      simp

/-- A continuous tail distribution commutes with head integration. This is the
non-axiomatic scalar Fubini theorem needed by the rooted E-to-R source
identity. -/
theorem continuousLinearMap_apply_sliceIntegralCLM_eq_integral
    {n : ℕ}
    (L : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    L (sliceIntegralCLM n F) =
      ∫ t : ℝ,
        L (schwartzPartialEval₁ (headTailProductSchwartzCLM n F) t) := by
  let T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    headSliceScalarCLM L
  have hfac :=
    map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
      T
      (isHeadTranslationInvariant_headSliceScalarCLM L)
      normedUnitBumpSchwartz
      integral_normedUnitBumpSchwartz
      F
  have hdes :
      headTranslationDescentCLM T normedUnitBumpSchwartz = L := by
    simpa [T] using headTranslationDescentCLM_headSliceScalarCLM L
  calc
    L (sliceIntegralCLM n F) = L (sliceIntegral F) := by
      rw [sliceIntegralCLM_apply]
    _ = headTranslationDescentCLM T normedUnitBumpSchwartz
          (sliceIntegral F) := by
      rw [hdes]
    _ = T F := hfac.symm
    _ = ∫ t : ℝ,
        L (schwartzPartialEval₁ (headTailProductSchwartzCLM n F) t) := by
      rfl

end SCV
