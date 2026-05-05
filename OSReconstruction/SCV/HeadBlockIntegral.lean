import OSReconstruction.SCV.TranslationDifferentiation

/-!
# Pure SCV Head-Block Integration

This file supplies the QFT-free real-coordinate block integral needed by the
distributional EOW kernel route.  It integrates a Schwartz function on
`Fin (m + n) -> R` over the first `m` coordinates and returns a Schwartz
function of the remaining `n` coordinates.
-/

noncomputable section

open scoped SchwartzMap LineDeriv
open MeasureTheory

namespace SCV

/-- Raw fiber integral over a finite real block, with the base variable first. -/
def realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V)
    (u : Fin n → ℝ) : V :=
  ∫ t : Fin m → ℝ, F (u, t)

@[simp]
theorem realFiberIntegralRaw_apply {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V)
    (u : Fin n → ℝ) :
    realFiberIntegralRaw F u = ∫ t : Fin m → ℝ, F (u, t) := by
  rfl

/-- Every fixed base fiber of a product-space Schwartz map is integrable. -/
theorem integrable_realFiber {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V)
    (u : Fin n → ℝ) :
    Integrable (fun t : Fin m → ℝ => F (u, t)) := by
  let μ : Measure (Fin m → ℝ) := volume
  have hmeas : AEStronglyMeasurable (fun t : Fin m → ℝ => F (u, t)) μ := by
    have hcont_pair : Continuous fun t : Fin m → ℝ => (u, t) := by
      exact continuous_const.prodMk continuous_id
    exact (F.continuous.comp hcont_pair).aestronglyMeasurable
  have hnorm : Integrable (fun t : Fin m → ℝ => ‖t‖ ^ 0 * ‖F (u, t)‖) μ := by
    refine integrable_of_le_of_pow_mul_le
      (μ := μ) (f := fun t : Fin m → ℝ => F (u, t))
      (C₁ := SchwartzMap.seminorm ℝ 0 0 F)
      (C₂ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 F) (k := 0)
      ?hf ?hpow hmeas
    · intro t
      have h := SchwartzMap.le_seminorm ℝ 0 0 F (u, t)
      simpa using h
    · intro t
      have ht_norm : ‖t‖ ≤ ‖(u, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖u‖ ‖t‖
      have hpow_le :
          ‖t‖ ^ (0 + μ.integrablePower) ≤ ‖(u, t)‖ ^ (0 + μ.integrablePower) :=
        pow_le_pow_left₀ (norm_nonneg _) ht_norm _
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 F (u, t)
      have h' :
          ‖(u, t)‖ ^ (0 + μ.integrablePower) * ‖F (u, t)‖ ≤
            SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 F := by
        simpa using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
  rw [← integrable_norm_iff hmeas]
  simpa using hnorm

/-- The base-variable derivative field of a real fiber product Schwartz map. -/
def realFiberBaseFDerivSchwartz {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    SchwartzMap
      ((Fin n → ℝ) × (Fin m → ℝ))
      ((Fin n → ℝ) →L[ℝ] V) :=
  (SchwartzMap.postcompCLM
    ((ContinuousLinearMap.inl ℝ
      (Fin n → ℝ) (Fin m → ℝ)).precomp V))
    (SchwartzMap.fderivCLM ℝ
      ((Fin n → ℝ) × (Fin m → ℝ)) V F)

@[simp]
theorem realFiberBaseFDerivSchwartz_apply {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V)
    (u : Fin n → ℝ) (t : Fin m → ℝ) :
    realFiberBaseFDerivSchwartz F (u, t) =
      (fderiv ℝ (F : ((Fin n → ℝ) × (Fin m → ℝ)) → V) (u, t)).comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ)) := by
  simp [realFiberBaseFDerivSchwartz]

/-- Zeroth-order weighted decay of the raw real fiber integral. -/
theorem exists_norm_pow_mul_realFiberIntegralRaw_le {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) (k : ℕ) :
    ∃ C, ∀ u : Fin n → ℝ,
      ‖u‖ ^ k * ‖realFiberIntegralRaw F u‖ ≤ C := by
  let μ : Measure (Fin m → ℝ) := volume
  let C₁ : ℝ := SchwartzMap.seminorm ℝ k 0 F
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (k + μ.integrablePower) 0 F
  refine ⟨2 ^ μ.integrablePower *
      (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂), ?_⟩
  intro u
  let c : ℝ := ‖u‖ ^ k
  have hbound :
      ∫ t : Fin m → ℝ, ‖t‖ ^ 0 * ‖c • F (u, t)‖ ∂μ ≤
        2 ^ μ.integrablePower *
          (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) := by
    refine integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
      (f := fun t : Fin m → ℝ => c • F (u, t)) (C₁ := C₁) (C₂ := C₂) ?hf ?hpow
    · intro t
      have hu_norm : ‖u‖ ≤ ‖(u, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖u‖ ‖t‖
      have hupow : ‖u‖ ^ k ≤ ‖(u, t)‖ ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hu_norm _
      have h := SchwartzMap.le_seminorm ℝ k 0 F (u, t)
      have h' : ‖(u, t)‖ ^ k * ‖F (u, t)‖ ≤ C₁ := by
        simpa [C₁] using h
      calc
        ‖c • F (u, t)‖ = c * ‖F (u, t)‖ := by
          simp [c, norm_smul]
        _ = ‖u‖ ^ k * ‖F (u, t)‖ := rfl
        _ ≤ ‖(u, t)‖ ^ k * ‖F (u, t)‖ :=
          mul_le_mul_of_nonneg_right hupow (norm_nonneg _)
        _ ≤ C₁ := h'
    · intro t
      have hu_norm : ‖u‖ ≤ ‖(u, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖u‖ ‖t‖
      have ht_norm : ‖t‖ ≤ ‖(u, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖u‖ ‖t‖
      have hprod :
          ‖t‖ ^ (0 + μ.integrablePower) * c ≤
            ‖(u, t)‖ ^ (k + μ.integrablePower) := by
        have ht_pow : ‖t‖ ^ μ.integrablePower ≤ ‖(u, t)‖ ^ μ.integrablePower :=
          pow_le_pow_left₀ (norm_nonneg _) ht_norm _
        have hu_pow : ‖u‖ ^ k ≤ ‖(u, t)‖ ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hu_norm _
        calc
          ‖t‖ ^ (0 + μ.integrablePower) * c = ‖t‖ ^ μ.integrablePower * ‖u‖ ^ k := by
            simp [c]
          _ ≤ ‖(u, t)‖ ^ μ.integrablePower * ‖(u, t)‖ ^ k :=
            mul_le_mul ht_pow hu_pow (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
          _ = ‖(u, t)‖ ^ (k + μ.integrablePower) := by
            rw [← pow_add]
            ring_nf
      have h := SchwartzMap.le_seminorm ℝ (k + μ.integrablePower) 0 F (u, t)
      have h' : ‖(u, t)‖ ^ (k + μ.integrablePower) * ‖F (u, t)‖ ≤ C₂ := by
        simpa [C₂] using h
      calc
        ‖t‖ ^ (0 + μ.integrablePower) * ‖c • F (u, t)‖
            = (‖t‖ ^ (0 + μ.integrablePower) * c) * ‖F (u, t)‖ := by
              simp [c, norm_smul, mul_assoc]
        _ ≤ ‖(u, t)‖ ^ (k + μ.integrablePower) * ‖F (u, t)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ C₂ := h'
  have hnorm_int : ‖realFiberIntegralRaw F u‖ ≤ ∫ t : Fin m → ℝ, ‖F (u, t)‖ := by
    simpa [realFiberIntegralRaw, μ] using
      (norm_integral_le_integral_norm (μ := μ) (f := fun t : Fin m → ℝ => F (u, t)))
  calc
    ‖u‖ ^ k * ‖realFiberIntegralRaw F u‖
        ≤ ‖u‖ ^ k * ∫ t : Fin m → ℝ, ‖F (u, t)‖ := by
          gcongr
    _ = ∫ t : Fin m → ℝ, ‖u‖ ^ k * ‖F (u, t)‖ := by
          rw [← integral_const_mul]
    _ = ∫ t : Fin m → ℝ, ‖t‖ ^ 0 * ‖c • F (u, t)‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          simp [c, norm_smul]
    _ ≤ 2 ^ μ.integrablePower *
          (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) :=
      hbound

lemma exists_integrable_bound_realFiberBaseFDerivSchwartz {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    ∃ bound : (Fin m → ℝ) → ℝ,
      Integrable bound ∧
      ∀ u t, ‖realFiberBaseFDerivSchwartz F (u, t)‖ ≤ bound t := by
  let μ : Measure (Fin m → ℝ) := volume
  let G : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) ((Fin n → ℝ) →L[ℝ] V) :=
    realFiberBaseFDerivSchwartz F
  let C₁ : ℝ := SchwartzMap.seminorm ℝ 0 0 G
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 G
  refine ⟨fun t => 2 ^ μ.integrablePower * (C₁ + C₂) *
      (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ)), ?_, ?_⟩
  · simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Measure.integrable_pow_neg_integrablePower μ).const_mul
        (2 ^ μ.integrablePower * (C₁ + C₂))
  · intro u t
    have h1 : ‖G (u, t)‖ ≤ C₁ := by
      have h := SchwartzMap.le_seminorm ℝ 0 0 G (u, t)
      simpa [G, C₁] using h
    have ht_norm : ‖t‖ ≤ ‖(u, t)‖ := by
      rw [Prod.norm_def]
      exact le_max_right ‖u‖ ‖t‖
    have hpow_le :
        ‖t‖ ^ (0 + μ.integrablePower) ≤ ‖(u, t)‖ ^ (0 + μ.integrablePower) :=
      pow_le_pow_left₀ (norm_nonneg _) ht_norm _
    have h2 : ‖t‖ ^ (0 + μ.integrablePower) * ‖G (u, t)‖ ≤ C₂ := by
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 G (u, t)
      have h' : ‖(u, t)‖ ^ (0 + μ.integrablePower) * ‖G (u, t)‖ ≤ C₂ := by
        simpa [G, C₂] using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
    have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := μ.integrablePower)
      (x := ‖t‖) (f := ‖G (u, t)‖) (C₁ := C₁) (C₂ := C₂)
      (norm_nonneg _) (norm_nonneg _) h1 h2
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hmain

theorem hasFDerivAt_realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V)
    (u : Fin n → ℝ) :
    HasFDerivAt (realFiberIntegralRaw F)
      (realFiberIntegralRaw (realFiberBaseFDerivSchwartz F) u) u := by
  obtain ⟨bound, hbound_int, hbound⟩ := exists_integrable_bound_realFiberBaseFDerivSchwartz F
  have hs : (Set.univ : Set (Fin n → ℝ)) ∈ nhds u := Filter.univ_mem
  have hF_meas :
      ∀ᶠ u' in nhds u,
        AEStronglyMeasurable (fun t : Fin m → ℝ => F (u', t))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) := by
    exact Filter.Eventually.of_forall fun u' =>
      (integrable_realFiber F u').aestronglyMeasurable
  have hF_int :
      Integrable (fun t : Fin m → ℝ => F (u, t))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) :=
    integrable_realFiber F u
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : Fin m → ℝ => realFiberBaseFDerivSchwartz F (u, t))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) :=
    (integrable_realFiber (realFiberBaseFDerivSchwartz F) u).aestronglyMeasurable
  have h_bound :
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
        ∀ u' ∈ (Set.univ : Set (Fin n → ℝ)),
          ‖realFiberBaseFDerivSchwartz F (u', t)‖ ≤ bound t := by
    exact Filter.Eventually.of_forall fun t u' _ => hbound u' t
  have h_diff :
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
        ∀ u' ∈ (Set.univ : Set (Fin n → ℝ)),
          HasFDerivAt (fun u'' : Fin n → ℝ => F (u'', t))
            (realFiberBaseFDerivSchwartz F (u', t)) u' := by
    refine Filter.Eventually.of_forall ?_
    intro t u' _
    let inl : (Fin n → ℝ) →L[ℝ]
        ((Fin n → ℝ) × (Fin m → ℝ)) :=
      ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ)
    have hinner : HasFDerivAt (fun u'' : Fin n → ℝ => (u'', t)) inl u' := by
      have hlin : HasFDerivAt (fun u'' : Fin n → ℝ => inl u'') inl u' :=
        inl.hasFDerivAt
      have hconst :
          (fun u'' : Fin n → ℝ => (u'', t)) = fun u'' => inl u'' + (0, t) := by
        funext u''
        ext i <;> simp [inl]
      rw [hconst]
      exact hlin.add_const (0, t)
    have hFderiv :
        HasFDerivAt (F : ((Fin n → ℝ) × (Fin m → ℝ)) → V)
          (fderiv ℝ (F : ((Fin n → ℝ) × (Fin m → ℝ)) → V) (u', t)) (u', t) :=
      F.differentiableAt.hasFDerivAt
    simpa [inl] using hFderiv.comp u' hinner
  simpa [realFiberIntegralRaw] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (s := (Set.univ : Set (Fin n → ℝ)))
      (x₀ := u)
      (F := fun u' t => F (u', t))
      (F' := fun u' t => realFiberBaseFDerivSchwartz F (u', t))
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff)

theorem fderiv_realFiberIntegralRaw_eq {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    fderiv ℝ (realFiberIntegralRaw F) =
      realFiberIntegralRaw (realFiberBaseFDerivSchwartz F) := by
  funext u
  exact (hasFDerivAt_realFiberIntegralRaw F u).fderiv

theorem continuous_realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    Continuous (realFiberIntegralRaw F) :=
  continuous_iff_continuousAt.2 fun u =>
    (hasFDerivAt_realFiberIntegralRaw F u).continuousAt

theorem contDiff_nat_realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (r : ℕ) (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    ContDiff ℝ r (realFiberIntegralRaw F) := by
  induction r generalizing V F with
  | zero =>
      exact contDiff_zero.2 (continuous_realFiberIntegralRaw F)
  | succ r ihr =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := r)
        (f := realFiberIntegralRaw F)).2 <| by
        refine ⟨realFiberIntegralRaw (realFiberBaseFDerivSchwartz F), ?_, ?_⟩
        · exact ihr (F := realFiberBaseFDerivSchwartz F)
        · intro u
          exact hasFDerivAt_realFiberIntegralRaw F u

theorem contDiff_realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) :
    ContDiff ℝ (⊤ : ℕ∞) (realFiberIntegralRaw F) := by
  rw [contDiff_infty]
  intro r
  exact contDiff_nat_realFiberIntegralRaw r F

theorem decay_realFiberIntegralRaw {m n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) V) (k r : ℕ) :
    ∃ C, ∀ u : Fin n → ℝ,
      ‖u‖ ^ k * ‖iteratedFDeriv ℝ r (realFiberIntegralRaw F) u‖ ≤ C := by
  induction r generalizing V F with
  | zero =>
      obtain ⟨C, hC⟩ := exists_norm_pow_mul_realFiberIntegralRaw_le F k
      refine ⟨C, fun u => ?_⟩
      simpa [norm_iteratedFDeriv_zero] using hC u
  | succ r ihr =>
      obtain ⟨C, hC⟩ := ihr (F := realFiberBaseFDerivSchwartz F)
      refine ⟨C, fun u => ?_⟩
      calc
        ‖u‖ ^ k * ‖iteratedFDeriv ℝ (r + 1) (realFiberIntegralRaw F) u‖
            = ‖u‖ ^ k *
                ‖iteratedFDeriv ℝ r (fderiv ℝ (realFiberIntegralRaw F)) u‖ := by
              rw [norm_iteratedFDeriv_fderiv]
        _ = ‖u‖ ^ k *
              ‖iteratedFDeriv ℝ r
                (realFiberIntegralRaw (realFiberBaseFDerivSchwartz F)) u‖ := by
              rw [fderiv_realFiberIntegralRaw_eq]
        _ ≤ C := hC u

/-- Fiber integration over a finite real block as a Schwartz map in the base. -/
def realFiberIntegral {m n : ℕ}
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ where
  toFun := realFiberIntegralRaw F
  smooth' := contDiff_realFiberIntegralRaw F
  decay' := decay_realFiberIntegralRaw F

@[simp]
theorem realFiberIntegral_apply {m n : ℕ}
    (F : SchwartzMap ((Fin n → ℝ) × (Fin m → ℝ)) ℂ)
    (u : Fin n → ℝ) :
    realFiberIntegral F u = ∫ t : Fin m → ℝ, F (u, t) := by
  rfl

/-- Product-to-flat coordinates sending `(tail, head)` to `Fin.append head tail`. -/
def headTailAppendCLE (m n : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃L[ℝ] (Fin (m + n) → ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) (Fin m → ℝ)).trans
    (finAppendCLE m n)

@[simp]
theorem headTailAppendCLE_apply {m n : ℕ}
    (u : Fin n → ℝ) (t : Fin m → ℝ) :
    headTailAppendCLE m n (u, t) = Fin.append t u := by
  ext i
  refine Fin.addCases (motive := fun i =>
    headTailAppendCLE m n (u, t) i = Fin.append t u i) ?_ ?_ i
  · intro j
    simp [headTailAppendCLE]
  · intro j
    simp [headTailAppendCLE]

/-- Integrate out the first `m` real coordinates of a Schwartz function. -/
def integrateHeadBlock {m n : ℕ}
    (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  realFiberIntegral
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (headTailAppendCLE m n)) F)

/-- A continuous Schwartz functional on `Fin (m + n) → ℝ` is invariant under
translations of the first `m` coordinates. -/
def IsHeadBlockTranslationInvariantSchwartzCLM {m n : ℕ}
    (T : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : Fin m → ℝ,
    T.comp (translateSchwartzCLM (headBlockShift m n a)) = T

@[simp]
theorem integrateHeadBlock_apply_finAppend {m n : ℕ}
    (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) (u : Fin n → ℝ) :
    integrateHeadBlock (m := m) (n := n) F u =
      ∫ t : Fin m → ℝ, F (Fin.append t u) := by
  simp [integrateHeadBlock, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp]
theorem integrateHeadBlock_zero {m n : ℕ} :
    integrateHeadBlock (m := m) (n := n) (0 : SchwartzMap (Fin (m + n) → ℝ) ℂ) =
      0 := by
  ext u
  simp [integrateHeadBlock_apply_finAppend]

theorem integrateHeadBlock_add {m n : ℕ}
    (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    integrateHeadBlock (m := m) (n := n) (F + G) =
      integrateHeadBlock (m := m) (n := n) F +
        integrateHeadBlock (m := m) (n := n) G := by
  ext u
  change integrateHeadBlock (m := m) (n := n) (F + G) u =
    integrateHeadBlock (m := m) (n := n) F u +
      integrateHeadBlock (m := m) (n := n) G u
  rw [integrateHeadBlock_apply_finAppend, integrateHeadBlock_apply_finAppend,
    integrateHeadBlock_apply_finAppend]
  have hF :
      Integrable
        (fun t : Fin m → ℝ =>
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (headTailAppendCLE m n)) F) (u, t)) :=
    integrable_realFiber
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (headTailAppendCLE m n)) F) u
  have hG :
      Integrable
        (fun t : Fin m → ℝ =>
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (headTailAppendCLE m n)) G) (u, t)) :=
    integrable_realFiber
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (headTailAppendCLE m n)) G) u
  simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    using MeasureTheory.integral_add hF hG

theorem integrateHeadBlock_sub {m n : ℕ}
    (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    integrateHeadBlock (m := m) (n := n) (F - G) =
      integrateHeadBlock (m := m) (n := n) F -
        integrateHeadBlock (m := m) (n := n) G := by
  ext u
  change integrateHeadBlock (m := m) (n := n) (F - G) u =
    integrateHeadBlock (m := m) (n := n) F u -
      integrateHeadBlock (m := m) (n := n) G u
  rw [integrateHeadBlock_apply_finAppend, integrateHeadBlock_apply_finAppend,
    integrateHeadBlock_apply_finAppend]
  have hF :
      Integrable
        (fun t : Fin m → ℝ =>
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (headTailAppendCLE m n)) F) (u, t)) :=
    integrable_realFiber
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (headTailAppendCLE m n)) F) u
  have hG :
      Integrable
        (fun t : Fin m → ℝ =>
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (headTailAppendCLE m n)) G) (u, t)) :=
    integrable_realFiber
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (headTailAppendCLE m n)) G) u
  simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    using MeasureTheory.integral_sub hF hG

/-- Adding a head-block shift to appended coordinates only translates the head
block. -/
theorem finAppend_add_headBlockShift {m n : ℕ}
    (t a : Fin m → ℝ) (u : Fin n → ℝ) :
    Fin.append t u + headBlockShift m n a = Fin.append (t + a) u := by
  ext i
  refine Fin.addCases (motive := fun i =>
    (Fin.append t u + headBlockShift m n a) i = Fin.append (t + a) u i) ?_ ?_ i
  · intro j
    simp [headBlockShift]
  · intro j
    simp [headBlockShift]

/-- Head-block integration is invariant under translating the integrated head
coordinates. -/
theorem integrateHeadBlock_translate_head {m n : ℕ}
    (a : Fin m → ℝ) (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    integrateHeadBlock (m := m) (n := n)
      (translateSchwartzCLM (headBlockShift m n a) F) =
    integrateHeadBlock (m := m) (n := n) F := by
  ext u
  rw [integrateHeadBlock_apply_finAppend, integrateHeadBlock_apply_finAppend]
  simp only [translateSchwartzCLM_apply, translateSchwartz_apply]
  rw [← MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure (Fin m → ℝ)))
    (f := fun t : Fin m → ℝ => F (Fin.append t u)) a]
  apply integral_congr_ae
  filter_upwards with t
  rw [finAppend_add_headBlockShift]

/-- Head-block-translation-invariant Schwartz functionals annihilate
directional derivatives along head-block coordinate directions. -/
theorem map_lineDeriv_headBlockShift_eq_zero {m n : ℕ}
    (T : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := n) T)
    (i : Fin m)
    (H : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
    T (LineDeriv.lineDerivOp
      (headBlockShift m n (Pi.single i (1 : ℝ))) H) = 0 := by
  let v : Fin (m + n) → ℝ := headBlockShift m n (Pi.single i (1 : ℝ))
  have hquot :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • v) H - H)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ))
        (nhds (T (LineDeriv.lineDerivOp v H))) :=
    (T.continuous.tendsto (LineDeriv.lineDerivOp v H)).comp
      (tendsto_diffQuotient_translateSchwartz_zero H v)
  have hzero :
      Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) :=
    tendsto_const_nhds
  have heq :
      (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • v) H - H))) =
        fun _ => (0 : ℂ) := by
    funext t
    have hv :
        t • v =
          headBlockShift m n (t • (Pi.single i (1 : ℝ) : Fin m → ℝ)) := by
      ext j
      refine Fin.addCases (motive := fun j =>
        (t • v) j =
          headBlockShift m n (t • (Pi.single i (1 : ℝ) : Fin m → ℝ)) j) ?_ ?_ j
      · intro k
        simp [v, headBlockShift]
      · intro k
        simp [v, headBlockShift]
    have htrans :
        T (translateSchwartz (t • v) H) = T H := by
      have hraw := congrArg
        (fun S : SchwartzMap (Fin (m + n) → ℝ) ℂ →L[ℂ] ℂ => S H)
        (hT (t • (Pi.single i (1 : ℝ) : Fin m → ℝ)))
      simpa [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply, hv] using hraw
    rw [T.map_smul_of_tower, map_sub, sub_eq_zero.mpr htrans]
    exact smul_zero (t⁻¹ : ℝ)
  have hzero' :
      Filter.Tendsto
        (fun t : ℝ => T (t⁻¹ • (translateSchwartz (t • v) H - H)))
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa only [heq] using hzero
  have hmain : T (LineDeriv.lineDerivOp v H) = 0 :=
    tendsto_nhds_unique hquot hzero'
  simpa [v] using hmain

end SCV
