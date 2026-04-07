import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Block Integration on Schwartz Space

This file packages two small pieces of infrastructure used when one wants to
integrate out an entire block of real coordinates from a Schwartz function:

- flattening/unflattening `n`-point Schwartz tests to ordinary Euclidean
  Schwartz space on `Fin (n * (d + 1)) -> R`
- repeated head-coordinate slice integration

The intended downstream use is the two-point center/difference descent
construction in the OS reconstruction lane.
-/

noncomputable section

open scoped SchwartzMap

namespace OSReconstruction

variable {d : ℕ}

private def uncurryLinearEquivBlock (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  { (Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private def flattenLinearEquivBlock (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (uncurryLinearEquivBlock n d 𝕜).trans
    (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

/-- The real flattening equivalence used by block integration. This is kept
local to avoid importing the heavier forward-tube distribution layer. -/
private def flattenCLEquivRealBlock (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (flattenLinearEquivBlock n d ℝ).toContinuousLinearEquiv

@[simp] private theorem flattenCLEquivRealBlock_apply (n d : ℕ)
    (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    flattenCLEquivRealBlock n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

@[simp] private theorem flattenCLEquivRealBlock_symm_apply (n d : ℕ)
    (w : Fin (n * d) → ℝ) (i : Fin n) (j : Fin d) :
    (flattenCLEquivRealBlock n d).symm w i j = w (finProdFinEquiv (i, j)) := rfl

private def flattenMeasurableEquivBlock (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃ᵐ (Fin (n * d) → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finProdFinEquiv)

@[simp] private theorem flattenMeasurableEquivBlock_apply (n d : ℕ)
    (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    flattenMeasurableEquivBlock n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [flattenMeasurableEquivBlock, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_curry_symm, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Function.uncurry]

private theorem volume_map_curry_symmBlock (n d : ℕ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin d → ℝ)).map
      (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm =
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n × Fin d → ℝ)) := by
  symm
  apply MeasureTheory.Measure.pi_eq
  intro s hs
  rw [MeasureTheory.Measure.map_apply
    (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have h_preimage : (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, MeasurableEquiv.coe_curry_symm,
      Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h ⟨i, j⟩ => h i j⟩
  rw [h_preimage, MeasureTheory.volume_pi_pi]
  simp_rw [MeasureTheory.volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

private theorem flattenMeasurableEquivBlock_measurePreserving (n d : ℕ) :
    MeasureTheory.MeasurePreserving (flattenMeasurableEquivBlock n d)
      MeasureTheory.volume MeasureTheory.volume := by
  have h_uncurry :
      MeasureTheory.MeasurePreserving
        (MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm
        MeasureTheory.volume MeasureTheory.volume := by
    refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d) ℝ).symm.measurable, ?_⟩
    exact volume_map_curry_symmBlock n d
  exact (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ => ℝ) finProdFinEquiv).comp h_uncurry

private theorem integral_flatten_change_of_variablesBlock (n d : ℕ)
    (g : (Fin (n * d) → ℝ) → ℂ) :
    ∫ x, g x = ∫ y, g (flattenCLEquivRealBlock n d y) := by
  rw [show (fun y => g (flattenCLEquivRealBlock n d y)) =
      (fun y => g (flattenMeasurableEquivBlock n d y)) from by
        ext y
        congr 1
        ext k
        simp [flattenMeasurableEquivBlock_apply, flattenCLEquivRealBlock_apply]]
  exact ((flattenMeasurableEquivBlock_measurePreserving n d).integral_comp' g).symm

/-- One-step Fubini / change-of-variables bridge for finite real blocks.

This packages the standard identification
`Fin (m + 1) → ℝ ≃ ℝ × (Fin m → ℝ)` at the level of Lebesgue integrals, in
the concrete form needed when recursively evaluating `integrateHeadBlock`.

The explicit product measure on the left is intentional: it keeps the theorem
usable in recursive block-integration proofs without relying on reducibility of
the ambient `volume` instance for product types. -/
theorem integral_finSucc_cons_eq
    {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℂ) :
    (∫ z : ℝ × (Fin m → ℝ), f (Fin.cons z.1 z.2)
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.Measure.pi fun _ : Fin m =>
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) =
      (∫ x : Fin (m + 1) → ℝ, f x
        ∂(MeasureTheory.Measure.pi fun _ : Fin (m + 1) =>
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
  have h :=
    ((MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0).symm).integral_comp'
      (g := f)
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Fin.cons_zero] using h

/-- Reindex a finite Euclidean block `Fin a -> R` along an equality `a = b`. -/
abbrev castFinCLE (h : a = b) : (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b => ℝ) (finCongr h)

/-- Reindex a Schwartz function along an equality of finite index sets. -/
abbrev reindexSchwartzFin (h : a = b) :
    SchwartzMap (Fin a → ℝ) ℂ →L[ℂ] SchwartzMap (Fin b → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE h).symm

@[simp] theorem reindexSchwartzFin_apply (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) (x : Fin b → ℝ) :
    reindexSchwartzFin h F x = F ((castFinCLE h).symm x) := rfl

@[simp] theorem castFinCLE_symm_apply (h : a = b)
    (x : Fin b → ℝ) (i : Fin a) :
    (castFinCLE h).symm x i = x ((finCongr h) i) := rfl

theorem integral_reindexSchwartzFin (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin b → ℝ)))
        (reindexSchwartzFin h F)
      =
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin a → ℝ))) F := by
  rw [SchwartzMap.integralCLM_apply, SchwartzMap.integralCLM_apply]
  let e : (Fin b → ℝ) ≃ᵐ (Fin a → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin a => ℝ) (finCongr h).symm
  have he :
      MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
    simpa [e] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Fin a => ℝ) (finCongr h).symm)
  simpa [reindexSchwartzFin, castFinCLE, e, MeasurableEquiv.piCongrLeft,
    ContinuousLinearEquiv.piCongrLeft] using
    (he.integral_comp' (f := e) (g := fun y : Fin a → ℝ => F y))

/-- Slice integration is additive on Schwartz functions. -/
theorem sliceIntegral_add {n : ℕ}
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    sliceIntegral (F + G) = sliceIntegral F + sliceIntegral G := by
  ext y
  change sliceIntegralRaw (F + G) y = sliceIntegralRaw F y + sliceIntegralRaw G y
  rw [sliceIntegralRaw, sliceIntegralRaw, sliceIntegralRaw]
  simpa using MeasureTheory.integral_add
    (integrable_sliceSection F y) (integrable_sliceSection G y)

/-- Slice integration commutes with subtraction on Schwartz functions. -/
theorem sliceIntegral_sub {n : ℕ}
    (F G : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    sliceIntegral (F - G) = sliceIntegral F - sliceIntegral G := by
  ext y
  change sliceIntegralRaw (F - G) y = sliceIntegralRaw F y - sliceIntegralRaw G y
  rw [sliceIntegralRaw, sliceIntegralRaw, sliceIntegralRaw]
  simpa using MeasureTheory.integral_sub
    (integrable_sliceSection F y) (integrable_sliceSection G y)

/-- Flatten an `n`-point Schwartz test to an ordinary Schwartz function on
`Fin (n * (d + 1)) -> R`. -/
abbrev flattenSchwartzNPoint {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivRealBlock n (d + 1)).symm

/-- Unflatten an ordinary Euclidean Schwartz function back to an `n`-point
Schwartz test. -/
abbrev unflattenSchwartzNPoint {n : ℕ} :
    SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenCLEquivRealBlock n (d + 1))

@[simp] theorem flattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzNPoint d n) (u : Fin (n * (d + 1)) → ℝ) :
    flattenSchwartzNPoint (d := d) f u = f ((flattenCLEquivRealBlock n (d + 1)).symm u) := rfl

@[simp] theorem unflattenSchwartzNPoint_apply {n : ℕ}
    (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ) (x : NPointDomain d n) :
    unflattenSchwartzNPoint (d := d) f x = f (flattenCLEquivRealBlock n (d + 1) x) := rfl

theorem integral_flattenSchwartzNPoint {n : ℕ}
    (f : SchwartzNPoint d n) :
    (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (n * (d + 1)) → ℝ)))
        (flattenSchwartzNPoint (d := d) f)
      =
    ∫ x : NPointDomain d n, f x := by
  rw [SchwartzMap.integralCLM_apply]
  simpa [flattenSchwartzNPoint_apply] using
    integral_flatten_change_of_variablesBlock n (d + 1)
      (flattenSchwartzNPoint (d := d) f)

/-- For two-point tests, flattening and then reindexing the ambient real block
into `(d+1) + (d+1)` recovers the expected block decomposition into the first
and second spacetime variables. -/
theorem reindex_flattenSchwartzNPoint_two_apply
    (f : SchwartzNPoint d 2) (x : Fin ((d + 1) + (d + 1)) → ℝ) :
    reindexSchwartzFin (by ring) (flattenSchwartzNPoint (d := d) f) x =
      f (fun i =>
        Fin.cases (splitFirst (d + 1) (d + 1) x)
          (fun _ => splitLast (d + 1) (d + 1) x) i) := by
  have h0 :
      ((flattenCLEquivRealBlock 2 (d + 1)).symm
          ((castFinCLE (by ring)).symm x) 0) =
        splitFirst (d + 1) (d + 1) x := by
    ext μ
    change x ((finCongr (by ring)).symm (finProdFinEquiv (0, μ))) = x (Fin.castAdd (d + 1) μ)
    refine congrArg x ?_
    apply Fin.ext
    simp [finProdFinEquiv]
  have h1 :
      ((flattenCLEquivRealBlock 2 (d + 1)).symm
          ((castFinCLE (by ring)).symm x) 1) =
        splitLast (d + 1) (d + 1) x := by
    ext μ
    change x ((finCongr (by ring)).symm (finProdFinEquiv (1, μ))) = x (Fin.natAdd (d + 1) μ)
    refine congrArg x ?_
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [reindexSchwartzFin_apply, flattenSchwartzNPoint_apply]
  congr 1
  ext i μ
  fin_cases i
  · simpa using congrArg (fun z : SpacetimeDim d => z μ) h0
  · simpa using congrArg (fun z : SpacetimeDim d => z μ) h1

/-- Repeatedly integrate out the first `m` real coordinates of a Schwartz
function on `Fin (m + n) -> R`. -/
noncomputable def integrateHeadBlock :
    {m n : ℕ} -> SchwartzMap (Fin (m + n) → ℝ) ℂ -> SchwartzMap (Fin n → ℝ) ℂ
  | 0, n, F => by
      exact reindexSchwartzFin (Nat.zero_add n) F
  | m + 1, n, F => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      let G : SchwartzMap (Fin (m + n) → ℝ) ℂ := sliceIntegral F'
      exact integrateHeadBlock (m := m) (n := n) G

/-- Block integration is additive on Schwartz functions. -/
theorem integrateHeadBlock_add :
    {m n : ℕ} -> (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n) (F + G) =
        integrateHeadBlock (m := m) (n := n) F +
          integrateHeadBlock (m := m) (n := n) G
  | 0, n, F, G => by
      simp [integrateHeadBlock]
  | m + 1, n, F, G => by
      simp [integrateHeadBlock, integrateHeadBlock_add, sliceIntegral_add]

/-- Block integration commutes with subtraction. -/
theorem integrateHeadBlock_sub :
    {m n : ℕ} -> (F G : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n) (F - G) =
        integrateHeadBlock (m := m) (n := n) F -
          integrateHeadBlock (m := m) (n := n) G
  | 0, n, F, G => by
      simp [integrateHeadBlock]
  | m + 1, n, F, G => by
      simp [integrateHeadBlock, integrateHeadBlock_sub, sliceIntegral_sub]

/-- Slice integration preserves pointwise real-valuedness. -/
theorem sliceIntegral_im_eq_zero_of_im_eq_zero {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF_real : ∀ x, (F x).im = 0) :
    ∀ y, (sliceIntegral F y).im = 0 := by
  intro y
  calc
    (sliceIntegral F y).im = ∫ t : ℝ, (F (Fin.cons t y)).im := by
      simpa [sliceIntegral_apply, sliceIntegralRaw] using
        (integral_im (integrable_sliceSection F y)).symm
    _ = 0 := by
      simp [hF_real]

/-- Slice integration preserves pointwise nonnegativity of the real part. -/
theorem sliceIntegral_re_nonneg_of_re_nonneg {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ)
    (hF_nonneg : ∀ x, 0 ≤ (F x).re) :
    ∀ y, 0 ≤ (sliceIntegral F y).re := by
  intro y
  calc
    0 ≤ ∫ t : ℝ, (F (Fin.cons t y)).re := by
      exact MeasureTheory.integral_nonneg fun t => hF_nonneg (Fin.cons t y)
    _ = (sliceIntegral F y).re := by
      simpa [sliceIntegral_apply, sliceIntegralRaw] using
        integral_re (integrable_sliceSection F y)

/-- Integrating out the head block preserves pointwise real-valuedness. -/
theorem integrateHeadBlock_im_eq_zero_of_im_eq_zero :
    {m n : ℕ} -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      (∀ x, (F x).im = 0) ->
      ∀ y, (integrateHeadBlock (m := m) (n := n) F y).im = 0
  | 0, n, F, hF_real, y => by
      simp [integrateHeadBlock, reindexSchwartzFin_apply, hF_real]
  | m + 1, n, F, hF_real, y => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      have hF'_real : ∀ x, (F' x).im = 0 := by
        intro x
        simp [F', reindexSchwartzFin_apply, hF_real]
      simpa [integrateHeadBlock, F'] using
        integrateHeadBlock_im_eq_zero_of_im_eq_zero
          (m := m) (n := n) (F := sliceIntegral F')
          (sliceIntegral_im_eq_zero_of_im_eq_zero F' hF'_real) y

/-- Integrating out the head block preserves pointwise nonnegativity of the
real part. -/
theorem integrateHeadBlock_re_nonneg_of_re_nonneg :
    {m n : ℕ} -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      (∀ x, 0 ≤ (F x).re) ->
      ∀ y, 0 ≤ (integrateHeadBlock (m := m) (n := n) F y).re
  | 0, n, F, hF_nonneg, y => by
      simpa [integrateHeadBlock, reindexSchwartzFin_apply] using
        hF_nonneg ((castFinCLE (Nat.zero_add n)).symm y)
  | m + 1, n, F, hF_nonneg, y => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      have hF'_nonneg : ∀ x, 0 ≤ (F' x).re := by
        intro x
        simp [F', reindexSchwartzFin_apply, hF_nonneg]
      simpa [integrateHeadBlock, F'] using
        integrateHeadBlock_re_nonneg_of_re_nonneg
          (m := m) (n := n) (F := sliceIntegral F')
          (sliceIntegral_re_nonneg_of_re_nonneg F' hF'_nonneg) y

/-- Reindexing a finite Euclidean block along an equality of index sets does
not enlarge a closed-ball support bound. -/
theorem reindexSchwartzFin_tsupport_subset_closedBall
    (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) {R : ℝ}
    (hF : tsupport (F : (Fin a → ℝ) → ℂ) ⊆ Metric.closedBall (0 : Fin a → ℝ) R) :
    tsupport ((reindexSchwartzFin h F : SchwartzMap (Fin b → ℝ) ℂ) :
        (Fin b → ℝ) → ℂ) ⊆
      Metric.closedBall (0 : Fin b → ℝ) R := by
  subst h
  simpa [reindexSchwartzFin] using hF

/-- A slice integral vanishes outside any closed ball containing the support of
the original Schwartz function. -/
theorem sliceIntegral_eq_zero_of_outside_closedBall {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) {R : ℝ}
    (hF : tsupport (F : (Fin (n + 1) → ℝ) → ℂ) ⊆
      Metric.closedBall (0 : Fin (n + 1) → ℝ) R)
    {y : Fin n → ℝ}
    (hy : y ∉ Metric.closedBall (0 : Fin n → ℝ) R) :
    sliceIntegral F y = 0 := by
  simpa [sliceIntegral_apply] using
    sliceIntegralRaw_eq_zero_of_outside_closedBall (F := F) (hF := hF) hy

/-- Integrating out the head block preserves any closed-ball support bound in
the remaining tail variables. This is the support control needed when a
two-point center/difference shell is descended to a one-variable test. -/
theorem integrateHeadBlock_tsupport_subset_closedBall :
    {m n : ℕ} -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) -> {R : ℝ} ->
      (tsupport (F : (Fin (m + n) → ℝ) → ℂ) ⊆
        Metric.closedBall (0 : Fin (m + n) → ℝ) R) ->
      tsupport ((integrateHeadBlock (m := m) (n := n) F :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ) ⊆
        Metric.closedBall (0 : Fin n → ℝ) R
  | 0, n, F, R, hF => by
      simpa [integrateHeadBlock] using
        reindexSchwartzFin_tsupport_subset_closedBall (h := Nat.zero_add n) F hF
  | m + 1, n, F, R, hF => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      have hF' :
          tsupport (F' : (Fin ((m + n) + 1) → ℝ) → ℂ) ⊆
            Metric.closedBall (0 : Fin ((m + n) + 1) → ℝ) R := by
        simpa [F'] using
          reindexSchwartzFin_tsupport_subset_closedBall
            (h := Nat.succ_add m n) F hF
      have hSlice :
          tsupport ((sliceIntegral F' : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
              (Fin (m + n) → ℝ) → ℂ) ⊆
            Metric.closedBall (0 : Fin (m + n) → ℝ) R := by
        intro y hy
        by_contra hyR
        have hnot :
            y ∉ tsupport ((sliceIntegral F' : SchwartzMap (Fin (m + n) → ℝ) ℂ) :
              (Fin (m + n) → ℝ) → ℂ) := by
          rw [notMem_tsupport_iff_eventuallyEq]
          have hOpen :
              IsOpen ((Metric.closedBall (0 : Fin (m + n) → ℝ) R)ᶜ) :=
            Metric.isClosed_closedBall.isOpen_compl
          refine Filter.mem_of_superset (hOpen.mem_nhds hyR) ?_
          intro z hz
          exact sliceIntegral_eq_zero_of_outside_closedBall
            (F := F') (hF := hF') hz
        exact hnot hy
      simpa [integrateHeadBlock, F'] using
        integrateHeadBlock_tsupport_subset_closedBall
          (m := m) (n := n) (F := sliceIntegral F') hSlice

/-- Iterated block integration preserves total Lebesgue integration. -/
theorem integral_integrateHeadBlock :
    {m n : ℕ} -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
          (integrateHeadBlock (m := m) (n := n) F)
        =
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (m + n) → ℝ))) F
  | 0, n, F => by
      simpa [integrateHeadBlock] using integral_reindexSchwartzFin (Nat.zero_add n) F
  | m + 1, n, F => by
      let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
        reindexSchwartzFin (Nat.succ_add m n) F
      let G : SchwartzMap (Fin (m + n) → ℝ) ℂ := sliceIntegral F'
      calc
        (SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
            (integrateHeadBlock (m := m + 1) (n := n) F)
            =
          (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin (m + n) → ℝ))) G := by
              simpa [integrateHeadBlock, F', G]
                using integral_integrateHeadBlock (m := m) (n := n) G
        _ =
          (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin ((m + n) + 1) → ℝ))) F' := by
              simpa [G] using integral_sliceIntegral F'
        _ =
          (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin ((m + 1) + n) → ℝ))) F := by
              simpa [F'] using integral_reindexSchwartzFin (Nat.succ_add m n) F

private theorem splitFirst_castFinCLE_succ_add_symm_cons {m n : ℕ}
    (t : ℝ) (x : Fin (m + n) → ℝ) :
    splitFirst (m + 1) n ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) =
      Fin.cons t (splitFirst m n x) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · have hcast :
        Fin.cast (Nat.succ_add m n) (Fin.castAdd n (0 : Fin (m + 1))) = 0 := by
          apply Fin.ext
          simp
    simp [splitFirst, hcast]
  · intro i
    have hcast :
        Fin.cast (Nat.succ_add m n) (Fin.castAdd n i.succ) = (Fin.castAdd n i).succ := by
          apply Fin.ext
          simp
    simp [splitFirst, hcast]

private theorem splitLast_castFinCLE_succ_add_symm_cons {m n : ℕ}
    (t : ℝ) (x : Fin (m + n) → ℝ) :
    splitLast (m + 1) n ((castFinCLE (Nat.succ_add m n)).symm (Fin.cons t x)) =
      splitLast m n x := by
  ext j
  have hcast :
      Fin.cast (Nat.succ_add m n) (Fin.natAdd (m + 1) j) = (Fin.natAdd m j).succ := by
        apply Fin.ext
        simp
        omega
  simp [splitLast, hcast]

private theorem splitFirst_castFinCLE_zero_add_symm {n : ℕ}
    (x : Fin n → ℝ) :
    splitFirst 0 n ((castFinCLE (Nat.zero_add n)).symm x) = default := by
  ext i
  exact Fin.elim0 i

private theorem splitLast_castFinCLE_zero_add_symm {n : ℕ}
    (x : Fin n → ℝ) :
    splitLast 0 n ((castFinCLE (Nat.zero_add n)).symm x) = x := by
  ext j
  simp [splitLast]

/-- Projection from a block `Fin (m + n) → ℝ` to its tail block of size `n`. -/
noncomputable def tailBlockCLM (m n : ℕ) :
    (Fin (m + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + n)) (φ := fun _ => ℝ) (Fin.natAdd m j)

@[simp] theorem tailBlockCLM_apply (m n : ℕ)
    (x : Fin (m + n) → ℝ) :
    tailBlockCLM m n x = splitLast m n x := by
  ext j
  simp [tailBlockCLM, splitLast]

/-- Slice integration commutes with multiplying by a Schwartz factor depending
only on the tail block. This is the one-step compatibility needed to push
center/difference descent through tail-only kernels. -/
theorem sliceIntegral_reindex_smulTail {m n : ℕ}
    (g : SchwartzMap (Fin n → ℝ) ℂ) (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    sliceIntegral
        (reindexSchwartzFin (Nat.succ_add m n)
          (SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin ((m + 1) + n) → ℝ => g (splitLast (m + 1) n x)) F)) =
      SchwartzMap.smulLeftCLM ℂ
        (fun x : Fin (m + n) → ℝ => g (splitLast m n x))
        (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) := by
  let htempSucc : (fun x : Fin ((m + 1) + n) → ℝ => g (splitLast (m + 1) n x)).HasTemperateGrowth := by
    simpa [tailBlockCLM_apply] using g.hasTemperateGrowth.comp (tailBlockCLM (m + 1) n).hasTemperateGrowth
  let htemp : (fun x : Fin (m + n) → ℝ => g (splitLast m n x)).HasTemperateGrowth := by
    simpa [tailBlockCLM_apply] using g.hasTemperateGrowth.comp (tailBlockCLM m n).hasTemperateGrowth
  ext x
  rw [sliceIntegral_apply, sliceIntegralRaw]
  rw [SchwartzMap.smulLeftCLM_apply_apply htemp]
  rw [sliceIntegral_apply, sliceIntegralRaw]
  have hfun :
      (fun t : ℝ =>
        (reindexSchwartzFin (Nat.succ_add m n)
          (SchwartzMap.smulLeftCLM ℂ
            (fun y : Fin ((m + 1) + n) → ℝ => g (splitLast (m + 1) n y)) F))
            (Fin.cons t x)) =
      (fun t : ℝ =>
        g (splitLast m n x) *
          (reindexSchwartzFin (Nat.succ_add m n) F) (Fin.cons t x)) := by
    funext t
    rw [reindexSchwartzFin_apply, SchwartzMap.smulLeftCLM_apply_apply htempSucc,
      splitLast_castFinCLE_succ_add_symm_cons (m := m) (n := n) t x]
    simp [reindexSchwartzFin_apply]
  rw [hfun, smul_eq_mul]
  exact MeasureTheory.integral_const_mul _ _

/-- Block integration commutes with multiplying by a tail-only Schwartz factor.
This upgrades the one-step slice statement to the full iterated head-block
descent. -/
theorem integrateHeadBlock_smulTail :
    {m n : ℕ} -> (g : SchwartzMap (Fin n → ℝ) ℂ) ->
      (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n)
          (SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin (m + n) → ℝ => g (splitLast m n x)) F) =
        SchwartzMap.smulLeftCLM ℂ g (integrateHeadBlock (m := m) (n := n) F)
  | 0, n, g, F => by
      let htemp0 : (fun x : Fin (0 + n) → ℝ => g (splitLast 0 n x)).HasTemperateGrowth := by
        simpa [tailBlockCLM_apply] using g.hasTemperateGrowth.comp (tailBlockCLM 0 n).hasTemperateGrowth
      ext x
      rw [integrateHeadBlock, reindexSchwartzFin_apply, SchwartzMap.smulLeftCLM_apply_apply htemp0,
        splitLast_castFinCLE_zero_add_symm, integrateHeadBlock, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
      simp
  | m + 1, n, g, F => by
      calc
        integrateHeadBlock (m := m + 1) (n := n)
            (SchwartzMap.smulLeftCLM ℂ
              (fun x : Fin ((m + 1) + n) → ℝ => g (splitLast (m + 1) n x)) F)
          =
            integrateHeadBlock (m := m) (n := n)
              (sliceIntegral
                (reindexSchwartzFin (Nat.succ_add m n)
                  (SchwartzMap.smulLeftCLM ℂ
                    (fun x : Fin ((m + 1) + n) → ℝ => g (splitLast (m + 1) n x)) F))) := by
                      simp [integrateHeadBlock]
        _ =
            integrateHeadBlock (m := m) (n := n)
              (SchwartzMap.smulLeftCLM ℂ
                (fun x : Fin (m + n) → ℝ => g (splitLast m n x))
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))) := by
                  rw [sliceIntegral_reindex_smulTail]
        _ =
            SchwartzMap.smulLeftCLM ℂ g
              (integrateHeadBlock (m := m) (n := n)
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))) := by
                  simpa using integrateHeadBlock_smulTail (m := m) (n := n) g
                    (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))
        _ =
            SchwartzMap.smulLeftCLM ℂ g (integrateHeadBlock (m := m + 1) (n := n) F) := by
              simp [integrateHeadBlock]

/-- Integrating the head coordinate of a reindexed tensor product acts only on
the left tensor factor. This is the one-step descent formula behind block
integration of center/difference shells. -/
theorem sliceIntegral_reindex_tensorProduct {m n : ℕ}
    (f : SchwartzMap (Fin (m + 1) → ℝ) ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ) :
    sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) (f.tensorProduct g)) =
      (sliceIntegral f).tensorProduct g := by
  ext x
  rw [sliceIntegral_apply, sliceIntegralRaw, SchwartzMap.tensorProduct_apply,
    sliceIntegral_apply, sliceIntegralRaw]
  have hleft :
      (fun t : ℝ => ((reindexSchwartzFin (Nat.succ_add m n) (f.tensorProduct g))
        (Fin.cons t x))) =
      (fun t : ℝ => f (Fin.cons t (splitFirst m n x)) * g (splitLast m n x)) := by
    funext t
    rw [reindexSchwartzFin_apply, SchwartzMap.tensorProduct_apply]
    rw [splitFirst_castFinCLE_succ_add_symm_cons (m := m) (n := n) t x,
      splitLast_castFinCLE_succ_add_symm_cons (m := m) (n := n) t x]
  rw [hleft]; exact MeasureTheory.integral_mul_const _ _

/-- Integrating out the full left block of a tensor product leaves the right
tensor factor, scaled by the total integral of the left factor. -/
theorem integrateHeadBlock_tensorProduct :
    {m n : ℕ} -> (f : SchwartzMap (Fin m → ℝ) ℂ) -> (g : SchwartzMap (Fin n → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n) (f.tensorProduct g) =
        ((SchwartzMap.integralCLM ℂ
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f) • g
  | 0, n, f, g => by
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      have h_int :
          (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ))) f =
          f default := by
        rw [SchwartzMap.integralCLM_apply]
        rw [hvol, MeasureTheory.integral_dirac]
      ext x
      rw [integrateHeadBlock, reindexSchwartzFin_apply, SchwartzMap.tensorProduct_apply,
        splitFirst_castFinCLE_zero_add_symm, splitLast_castFinCLE_zero_add_symm, h_int]
      simp
  | m + 1, n, f, g => by
      calc
        integrateHeadBlock (m := m + 1) (n := n) (f.tensorProduct g)
            =
          integrateHeadBlock (m := m) (n := n) ((sliceIntegral f).tensorProduct g) := by
              simp [integrateHeadBlock, sliceIntegral_reindex_tensorProduct]
        _ =
          ((SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) (sliceIntegral f)) • g := by
              simpa using integrateHeadBlock_tensorProduct (m := m) (n := n) (sliceIntegral f) g
        _ =
          ((SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin (m + 1) → ℝ))) f) • g := by
              rw [integral_sliceIntegral]

/-- Integrating the head coordinate commutes with translating only the tail
coordinates. This is the one-step tail-translation invariance needed for the
two-point center/difference descent operator. -/
theorem sliceIntegral_translateSchwartz_cons_zero {n : ℕ}
    (a : Fin n → ℝ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    sliceIntegral (SCV.translateSchwartz (Fin.cons 0 a) F) =
      SCV.translateSchwartz a (sliceIntegral F) := by
  ext y
  rw [sliceIntegral_apply, sliceIntegralRaw, SCV.translateSchwartz_apply,
    sliceIntegral_apply, sliceIntegralRaw]
  have hfun :
      (fun x : ℝ => (SCV.translateSchwartz (Fin.cons 0 a) F) (Fin.cons x y)) =
        (fun x : ℝ => F (Fin.cons x (y + a))) := by
          funext x
          rw [SCV.translateSchwartz_apply]
          congr 1
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [Pi.add_apply]
          · intro i
            simp [Pi.add_apply]
  rw [hfun]

/-- Integrating the head coordinate is invariant under translating only that
coordinate. This is the one-step head-translation invariance needed to factor
head-translation-invariant functionals through block descent. -/
theorem sliceIntegral_translateSchwartz_head {n : ℕ}
    (a : ℝ) (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) :
    sliceIntegral (SCV.translateSchwartz (Fin.cons a 0) F) =
      sliceIntegral F := by
  ext y
  rw [sliceIntegral_apply, sliceIntegralRaw, sliceIntegral_apply, sliceIntegralRaw]
  have hfun :
      (fun x : ℝ => (SCV.translateSchwartz (Fin.cons a 0) F) (Fin.cons x y)) =
        (fun x : ℝ => F (Fin.cons (x + a) y)) := by
          funext x
          rw [SCV.translateSchwartz_apply]
          congr 1
          ext j
          refine Fin.cases ?_ ?_ j
          · simp [Pi.add_apply]
          · intro i
            simp [Pi.add_apply]
  rw [hfun]
  simpa [add_comm, add_left_comm, add_assoc] using
    (MeasureTheory.integral_add_right_eq_self
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (fun x : ℝ => F (Fin.cons x y)) a)

/-- Insert a pure tail translation vector into a block `Fin (m + n) -> ℝ` by
padding the head block with zeros. -/
def zeroHeadBlockShift : {m n : ℕ} -> (Fin n → ℝ) -> Fin (m + n) → ℝ
  | 0, n, a => (castFinCLE (Nat.zero_add n)).symm a
  | m + 1, n, a =>
      (castFinCLE (Nat.succ_add m n)).symm
        (Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a))

/-- Insert a pure head translation vector into a block `Fin (m + n) → ℝ` by
padding the tail block with zeros. -/
def zeroTailBlockShift : {m n : ℕ} -> (Fin m → ℝ) -> Fin (m + n) → ℝ
  | 0, n, a => by
      exact 0
  | m + 1, n, a =>
      (castFinCLE (Nat.succ_add m n)).symm
        (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)))

@[simp] theorem splitFirst_add {m n : ℕ}
    (x y : Fin (m + n) → ℝ) :
    splitFirst m n (x + y) = splitFirst m n x + splitFirst m n y := by
  ext i
  simp [splitFirst, Pi.add_apply]

@[simp] theorem splitLast_add {m n : ℕ}
    (x y : Fin (m + n) → ℝ) :
    splitLast m n (x + y) = splitLast m n x + splitLast m n y := by
  ext j
  simp [splitLast, Pi.add_apply]

@[simp] theorem splitFirst_zeroHeadBlockShift_eq_zero {m n : ℕ}
    (a : Fin n → ℝ) :
    splitFirst m n (zeroHeadBlockShift (m := m) (n := n) a) = 0 := by
  induction m generalizing a with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ m ihm =>
      rw [zeroHeadBlockShift, splitFirst_castFinCLE_succ_add_symm_cons]
      ext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro i
        simpa using congrArg (fun z : Fin m → ℝ => z i) (ihm a)

@[simp] theorem splitLast_zeroHeadBlockShift_eq {m n : ℕ}
    (a : Fin n → ℝ) :
    splitLast m n (zeroHeadBlockShift (m := m) (n := n) a) = a := by
  induction m generalizing a with
  | zero =>
      ext j
      simp [splitLast, zeroHeadBlockShift]
  | succ m ihm =>
      rw [zeroHeadBlockShift, splitLast_castFinCLE_succ_add_symm_cons]
      simpa using ihm a

@[simp] theorem splitFirst_zeroTailBlockShift_eq {m n : ℕ}
    (a : Fin m → ℝ) :
    splitFirst m n (zeroTailBlockShift (m := m) (n := n) a) = a := by
  induction m with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ m ihm =>
      rw [zeroTailBlockShift, splitFirst_castFinCLE_succ_add_symm_cons]
      ext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro i
        simpa using congrArg (fun z : Fin m → ℝ => z i) (ihm (fun j => a j.succ))

@[simp] theorem splitLast_zeroTailBlockShift_eq_zero {m n : ℕ}
    (a : Fin m → ℝ) :
    splitLast m n (zeroTailBlockShift (m := m) (n := n) a) = 0 := by
  induction m with
  | zero =>
      ext j
      simp [splitLast, zeroTailBlockShift]
  | succ m ihm =>
      rw [zeroTailBlockShift, splitLast_castFinCLE_succ_add_symm_cons]
      simpa using ihm (fun i => a i.succ)

@[simp] theorem splitFirst_zeroHeadBlockShift {m n : ℕ}
    (a : Fin n → ℝ) (x : Fin (m + n) → ℝ) :
    splitFirst m n (x + zeroHeadBlockShift (m := m) (n := n) a) =
      splitFirst m n x := by
  simp

@[simp] theorem splitLast_zeroHeadBlockShift {m n : ℕ}
    (a : Fin n → ℝ) (x : Fin (m + n) → ℝ) :
    splitLast m n (x + zeroHeadBlockShift (m := m) (n := n) a) =
      splitLast m n x + a := by
  simp

@[simp] theorem splitFirst_zeroTailBlockShift {m n : ℕ}
    (a : Fin m → ℝ) (x : Fin (m + n) → ℝ) :
    splitFirst m n (x + zeroTailBlockShift (m := m) (n := n) a) =
      splitFirst m n x + a := by
  simp

@[simp] theorem splitLast_zeroTailBlockShift {m n : ℕ}
    (a : Fin m → ℝ) (x : Fin (m + n) → ℝ) :
    splitLast m n (x + zeroTailBlockShift (m := m) (n := n) a) =
      splitLast m n x := by
  simp

private theorem reindex_translate_zeroHeadBlockShift_succ {m n : ℕ}
    (a : Fin n → ℝ) (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n)
        (SCV.translateSchwartz (zeroHeadBlockShift (m := m + 1) (n := n) a) F) =
      SCV.translateSchwartz (Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a))
        (reindexSchwartzFin (Nat.succ_add m n) F) := by
  ext x
  rw [reindexSchwartzFin_apply, SCV.translateSchwartz_apply,
    SCV.translateSchwartz_apply, reindexSchwartzFin_apply]
  congr 1

private theorem reindex_translate_zeroTailBlockShift_succ {m n : ℕ}
    (a : Fin (m + 1) → ℝ) (F : SchwartzMap (Fin ((m + 1) + n) → ℝ) ℂ) :
    reindexSchwartzFin (Nat.succ_add m n)
        (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a) F) =
      SCV.translateSchwartz
        (Fin.cons (a 0) (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)))
        (reindexSchwartzFin (Nat.succ_add m n) F) := by
  ext x
  simp [reindexSchwartzFin_apply, SCV.translateSchwartz_apply, zeroTailBlockShift]

/-- Block integration commutes with translating only the tail block. -/
theorem integrateHeadBlock_translateSchwartz_tail :
    {m n : ℕ} -> (a : Fin n → ℝ) -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n)
          (SCV.translateSchwartz (zeroHeadBlockShift (m := m) (n := n) a) F) =
        SCV.translateSchwartz a (integrateHeadBlock (m := m) (n := n) F)
  | 0, n, a, F => by
      ext x
      rw [integrateHeadBlock, reindexSchwartzFin_apply, integrateHeadBlock]
      simp [SCV.translateSchwartz_apply, zeroHeadBlockShift]
  | m + 1, n, a, F => by
      calc
        integrateHeadBlock (m := m + 1) (n := n)
            (SCV.translateSchwartz (zeroHeadBlockShift (m := m + 1) (n := n) a) F)
          =
            integrateHeadBlock (m := m) (n := n)
              (sliceIntegral
                (reindexSchwartzFin (Nat.succ_add m n)
                  (SCV.translateSchwartz (zeroHeadBlockShift (m := m + 1) (n := n) a) F))) := by
                    simp [integrateHeadBlock]
        _ =
            integrateHeadBlock (m := m) (n := n)
              (SCV.translateSchwartz
                (zeroHeadBlockShift (m := m) (n := n) a)
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))) := by
                  congr 1
                  calc
                    sliceIntegral
                        (reindexSchwartzFin (Nat.succ_add m n)
                          (SCV.translateSchwartz
                            (zeroHeadBlockShift (m := m + 1) (n := n) a) F))
                      =
                        sliceIntegral
                          (SCV.translateSchwartz
                            (Fin.cons 0 (zeroHeadBlockShift (m := m) (n := n) a))
                            (reindexSchwartzFin (Nat.succ_add m n) F)) := by
                              simpa using congrArg sliceIntegral
                                (reindex_translate_zeroHeadBlockShift_succ
                                  (m := m) (n := n) a F)
                    _ =
                        SCV.translateSchwartz
                          (zeroHeadBlockShift (m := m) (n := n) a)
                          (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) := by
                              simpa using
                                sliceIntegral_translateSchwartz_cons_zero
                                  (a := zeroHeadBlockShift (m := m) (n := n) a)
                                  (F := reindexSchwartzFin (Nat.succ_add m n) F)
        _ =
            SCV.translateSchwartz a
              (integrateHeadBlock (m := m) (n := n)
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))) := by
                  simpa using integrateHeadBlock_translateSchwartz_tail
                    (m := m) (n := n) a
                    (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))
        _ = SCV.translateSchwartz a (integrateHeadBlock (m := m + 1) (n := n) F) := by
              simp [integrateHeadBlock]

/-- Block integration is invariant under translating only the head block. -/
theorem integrateHeadBlock_translateSchwartz_head :
    {m n : ℕ} -> (a : Fin m → ℝ) -> (F : SchwartzMap (Fin (m + n) → ℝ) ℂ) ->
      integrateHeadBlock (m := m) (n := n)
          (SCV.translateSchwartz (zeroTailBlockShift (m := m) (n := n) a) F) =
        integrateHeadBlock (m := m) (n := n) F
  | 0, n, a, F => by
      ext x
      simp [integrateHeadBlock, zeroTailBlockShift]
  | m + 1, n, a, F => by
      calc
        integrateHeadBlock (m := m + 1) (n := n)
            (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a) F)
          =
            integrateHeadBlock (m := m) (n := n)
              (sliceIntegral
                (reindexSchwartzFin (Nat.succ_add m n)
                  (SCV.translateSchwartz (zeroTailBlockShift (m := m + 1) (n := n) a) F))) := by
                    simp [integrateHeadBlock]
        _ =
            integrateHeadBlock (m := m) (n := n)
              (SCV.translateSchwartz
                (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ))
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))) := by
                  congr 1
                  exact
                    calc
                      sliceIntegral
                          (reindexSchwartzFin (Nat.succ_add m n)
                            (SCV.translateSchwartz
                              (zeroTailBlockShift (m := m + 1) (n := n) a) F))
                      =
                        sliceIntegral
                          (SCV.translateSchwartz
                            (Fin.cons (a 0)
                              (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)))
                            (reindexSchwartzFin (Nat.succ_add m n) F)) := by
                              simpa using congrArg sliceIntegral
                                (reindex_translate_zeroTailBlockShift_succ
                                  (m := m) (n := n) a F)
                    _ =
                        SCV.translateSchwartz
                          (zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ))
                          (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) := by
                              let ashift : Fin (m + n) → ℝ :=
                                zeroTailBlockShift (m := m) (n := n) (fun i => a i.succ)
                              let F' : SchwartzMap (Fin ((m + n) + 1) → ℝ) ℂ :=
                                reindexSchwartzFin (Nat.succ_add m n) F
                              have hsplit :
                                  SCV.translateSchwartz (Fin.cons (a 0) ashift) F' =
                                    SCV.translateSchwartz (Fin.cons 0 ashift)
                                      (SCV.translateSchwartz (Fin.cons (a 0) 0) F') := by
                                ext x
                                rw [SCV.translateSchwartz_apply, SCV.translateSchwartz_apply,
                                  SCV.translateSchwartz_apply]
                                congr 1
                                ext j
                                refine Fin.cases ?_ ?_ j
                                · simp [Pi.add_apply]
                                · intro i
                                  simp [Pi.add_apply, add_left_comm, add_comm]
                              rw [hsplit, sliceIntegral_translateSchwartz_cons_zero]
                              exact congrArg (SCV.translateSchwartz ashift)
                                (sliceIntegral_translateSchwartz_head
                                  (a := a 0) (F := F'))
        _ =
            integrateHeadBlock (m := m) (n := n)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F)) := by
                simpa using integrateHeadBlock_translateSchwartz_head
                  (m := m) (n := n) (fun i => a i.succ)
                  (sliceIntegral (reindexSchwartzFin (Nat.succ_add m n) F))
        _ = integrateHeadBlock (m := m + 1) (n := n) F := by
              simp [integrateHeadBlock]

end OSReconstruction
