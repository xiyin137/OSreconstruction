import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SliceIntegral

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

end OSReconstruction
