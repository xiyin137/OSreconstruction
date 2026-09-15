/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.SpectralCondition
import OSReconstruction.Wightman.Spacetime.MinkowskiGeometry
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.ForwardTubeDomain
import OSReconstruction.ComplexLieGroups.BHWCore
import OSReconstruction.ComplexLieGroups.DifferenceCoordinates
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
























noncomputable section

open MeasureTheory Complex Filter Set Topology Module OSReconstruction



variable {d : ℕ} [NeZero d]












/-- The Euclidean inner product on spacetime (no Minkowski sign flip):
    `⟨η, p⟩_Eucl = ∑_μ η(μ) · p(μ)`. -/
def euclideanDot (η p : Fin (d + 1) → ℝ) : ℝ :=
  ∑ μ, η μ * p μ

/-- **Self-duality of the closed forward cone (qualitative).**
    For `y, p ∈ V̄₊`, the Euclidean dot product `∑_μ y(μ) · p(μ) ≥ 0`.

    Proof: `y₀p₀ ≥ √(spatialNormSq y) · √(spatialNormSq p) ≥ |spatialInner y p|`
    by Cauchy-Schwarz. So `euclideanDot y p = y₀p₀ + spatialInner y p ≥ 0`. -/
lemma euclideanDot_nonneg_closedCone
    (y : Fin (d + 1) → ℝ) (hy : y ∈ ForwardMomentumCone d)
    (p : Fin (d + 1) → ℝ) (hp : p ∈ ForwardMomentumCone d) :
    euclideanDot y p ≥ 0 := by
  -- Unpack V̄₊ membership: causal + forward
  simp only [ForwardMomentumCone, MinkowskiSpace.ClosedForwardLightCone,
    MinkowskiSpace.ForwardLightCone, Set.mem_setOf_eq,
    MinkowskiSpace.IsCausal, MinkowskiSpace.timeComponent] at hy hp
  have hy0 : y 0 ≥ 0 := hy.2
  have hp0 : p 0 ≥ 0 := hp.2
  have hy_spatial : MinkowskiSpace.spatialNormSq d y ≤ (y 0) ^ 2 := by
    have := MinkowskiSpace.minkowskiNormSq_decomp d y; linarith [hy.1]
  have hp_spatial : MinkowskiSpace.spatialNormSq d p ≤ (p 0) ^ 2 := by
    have := MinkowskiSpace.minkowskiNormSq_decomp d p; linarith [hp.1]
  -- Decompose euclideanDot = y₀p₀ + spatialInner
  have h_decomp : euclideanDot y p = y 0 * p 0 + MinkowskiSpace.spatialInner d y p := by
    simp only [euclideanDot, MinkowskiSpace.spatialInner, Fin.sum_univ_succ]
  rw [h_decomp]
  -- Cauchy-Schwarz: (spatialInner y p)² ≤ spatialNormSq y * spatialNormSq p ≤ (y₀ p₀)²
  have hcs := MinkowskiSpace.spatial_cauchy_schwarz d y p
  have h_sq_le : (MinkowskiSpace.spatialInner d y p) ^ 2 ≤ (y 0 * p 0) ^ 2 := by
    calc (MinkowskiSpace.spatialInner d y p) ^ 2
        ≤ MinkowskiSpace.spatialNormSq d y * MinkowskiSpace.spatialNormSq d p := hcs
      _ ≤ (y 0) ^ 2 * (p 0) ^ 2 := mul_le_mul hy_spatial hp_spatial
          (MinkowskiSpace.spatialNormSq_nonneg d p) (sq_nonneg _)
      _ = (y 0 * p 0) ^ 2 := by ring
  -- spatialInner y p ≥ -(y₀ p₀), so y₀p₀ + spatialInner ≥ 0
  have := (abs_le_of_sq_le_sq' h_sq_le (mul_nonneg hy0 hp0)).1
  linarith

/-- Smooth cutoff for the product forward momentum cone V̄₊ⁿ.
    Satisfies: χ = 1 on V̄₊ⁿ, 0 ≤ χ ≤ 1, C∞, supported in a neighborhood
    of V̄₊ⁿ. Built as product of single-cone cutoffs using `Real.smoothTransition`
    (cf. `SCV.smoothCutoff` in `FourierLaplaceCore.lean`). -/
private noncomputable def productConeCutoff (n : ℕ) :
    (Fin n → Fin (d + 1) → ℝ) → ℝ :=
  fun q => ∏ k : Fin n,
    Real.smoothTransition (q k 0 + 1) *
    Real.smoothTransition (-(MinkowskiSpace.minkowskiNormSq d (q k)) + 1)

private noncomputable def flatPositiveRescaleCLE (m : ℕ) :
    (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  let a : ℝˣ := Units.mk0 ((1 / (2 * Real.pi) : ℝ)) <| by
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  ContinuousLinearEquiv.smulLeft a







private abbrev BasepointSpace (d : ℕ) := Fin (d + 1) → ℝ

/-- A normalized Schwartz bump on the basepoint variable. This is the cutoff
used to choose a section of `diffVarReduction`. The implementation should
eventually follow the local `normedUnitBumpSchwartzPi` pattern recorded in the
blueprint. -/
private noncomputable def normedUnitBumpSchwartzLocal :
    SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private lemma integral_normedUnitBumpSchwartzLocal :
    ∫ x : ℝ, normedUnitBumpSchwartzLocal x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartzLocal x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    change (hf_compact.toSchwartzMap hf_smooth) x = _
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

private noncomputable def normedUnitBumpSchwartzPi : ∀ k : ℕ,
    SchwartzMap (Fin k → ℝ) ℂ
  | 0 => by
      let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
      have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
        simpa [f] using
          (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
      have hf_compact : HasCompactSupport f := by
        simpa [HasCompactSupport, tsupport, Function.support, f] using
          (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
      exact hf_compact.toSchwartzMap hf_smooth
  | k + 1 => normedUnitBumpSchwartzLocal.prependField (normedUnitBumpSchwartzPi k)

private lemma integral_normedUnitBumpSchwartzPi :
    ∀ k : ℕ, ∫ x : Fin k → ℝ, normedUnitBumpSchwartzPi k x = 1
  | 0 => by
      have happly :
          (fun x : Fin 0 → ℝ => normedUnitBumpSchwartzPi 0 x) =
            fun _ : Fin 0 → ℝ => (1 : ℂ) := by
        funext x
        rw [normedUnitBumpSchwartzPi]
        rfl
      rw [happly]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      simpa [hvol] using
        (MeasureTheory.integral_dirac (a := default) (f := fun _ : Fin 0 → ℝ => (1 : ℂ)))
  | k + 1 => by
      calc
        ∫ x : Fin (k + 1) → ℝ, normedUnitBumpSchwartzPi (k + 1) x
            =
          ∫ z : ℝ × (Fin k → ℝ), normedUnitBumpSchwartzPi (k + 1) (Fin.cons z.1 z.2) := by
              rw [MeasureTheory.volume_pi, MeasureTheory.Measure.volume_eq_prod]
              exact (OSReconstruction.integral_finSucc_cons_eq
                (f := fun x : Fin (k + 1) → ℝ => normedUnitBumpSchwartzPi (k + 1) x)).symm
        _ = ∫ z : ℝ × (Fin k → ℝ),
              normedUnitBumpSchwartzLocal z.1 * normedUnitBumpSchwartzPi k z.2 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              simp [normedUnitBumpSchwartzPi, SchwartzMap.prependField_apply]
        _ = (∫ x : ℝ, normedUnitBumpSchwartzLocal x) *
              (∫ y : Fin k → ℝ, normedUnitBumpSchwartzPi k y) := by
              rw [MeasureTheory.volume_pi, MeasureTheory.Measure.volume_eq_prod]
              exact MeasureTheory.integral_prod_mul
                (f := fun x : ℝ => normedUnitBumpSchwartzLocal x)
                (g := fun y : Fin k → ℝ => normedUnitBumpSchwartzPi k y)
        _ = 1 := by
              rw [integral_normedUnitBumpSchwartzLocal, integral_normedUnitBumpSchwartzPi k]
              ring

private noncomputable def normalizedBasepointBump (d : ℕ) :
    SchwartzMap (BasepointSpace d) ℂ :=
  normedUnitBumpSchwartzPi (d + 1)

private lemma integral_normalizedBasepointBump (d : ℕ) :
    ∫ a : BasepointSpace d, normalizedBasepointBump d a = 1 := by
  simpa [normalizedBasepointBump] using integral_normedUnitBumpSchwartzPi (d + 1)

private noncomputable def basepointDiffCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d (n + 1) ≃L[ℝ] (Fin (n + 1) → BasepointSpace d) where
  toFun x := Fin.cons (x 0) (fun k => fun μ => x k.succ μ - x k.castSucc μ)
  invFun y k μ := y 0 μ + diffVarSection d n (fun i => y i.succ) k μ
  left_inv := by
    intro x; ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      suffices h : ∀ j : Fin (n + 1),
          x 0 μ + diffVarSection d n (fun l ν => x l.succ ν - x l.castSucc ν) j μ = x j μ from
        h i.succ
      intro j; induction j using Fin.induction with
      | zero => simp [diffVarSection_zero]
      | succ j ih =>
          have hsucc := diffVarSection_succ (d := d) n (fun l ν => x l.succ ν - x l.castSucc ν) j μ
          linarith
  right_inv := by
    intro y; ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      change (y 0 μ + diffVarSection d n (fun j => y j.succ) i.succ μ) -
          (y 0 μ + diffVarSection d n (fun j => y j.succ) i.castSucc μ) = y i.succ μ
      rw [diffVarSection_succ]
      ring
  map_add' := by
    intro x y
    ext k μ <;> refine Fin.cases ?_ ?_ k <;> simp [Pi.add_apply, add_sub_add_comm]
  map_smul' := by
    intro c x
    ext k μ <;> refine Fin.cases ?_ ?_ k <;> simp [Pi.smul_apply, smul_sub, mul_sub]
  continuous_toFun := by
    apply continuous_pi; intro k; refine Fin.cases ?_ ?_ k
    · simp only [Fin.cons_zero]
      exact continuous_apply 0
    · intro i; simp only [Fin.cons_succ]
      exact continuous_pi fun μ =>
        (continuous_apply_apply i.succ μ).sub (continuous_apply_apply i.castSucc μ)
  continuous_invFun := by
    apply continuous_pi; intro k; apply continuous_pi; intro μ
    apply Continuous.add
    · exact (continuous_apply μ).comp (continuous_apply 0)
    · exact (continuous_apply μ).comp ((continuous_apply k).comp
        ((diffVarSection d n).continuous.comp
          (continuous_pi fun i => continuous_apply i.succ)))

@[simp] private lemma basepointDiffCLE_apply_zero (d : ℕ) (n : ℕ)
    (x : NPointSpacetime d (n + 1)) :
    basepointDiffCLE d n x 0 = x 0 := rfl

@[simp] private lemma basepointDiffCLE_apply_succ (d : ℕ) (n : ℕ)
    (x : NPointSpacetime d (n + 1)) (k : Fin n) :
    basepointDiffCLE d n x k.succ = fun μ => x k.succ μ - x k.castSucc μ := rfl

/-- A chosen Schwartz section of `diffVarReduction`. This should eventually be
implemented by transporting the tensor product `(a, ξ) ↦ φ₀(a) g(ξ)` back from
basepoint-plus-difference coordinates. -/
private noncomputable def sectionOf (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) :
    SchwartzNPointSpace d n → SchwartzNPointSpace d (n + 1) :=
  fun g =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffCLE d n)
      (φ₀.prependField g)

private noncomputable def sectionOfCLM (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) :
    SchwartzNPointSpace d n →L[ℂ] SchwartzNPointSpace d (n + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffCLE d n)).comp
    (SchwartzMap.prependFieldCLMRight φ₀)

@[simp] private lemma sectionOfCLM_apply (d : ℕ) (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ) (g : SchwartzNPointSpace d n) :
    sectionOfCLM d n φ₀ g = sectionOf d n φ₀ g := rfl

/-- The chosen section is a right inverse to `diffVarReduction` once the bump
has total integral `1`. -/
private lemma diffVarReduction_sectionOf (d : ℕ) [NeZero d] (n : ℕ)
    (φ₀ : SchwartzMap (BasepointSpace d) ℂ)
    (hφ₀ : ∫ a : BasepointSpace d, φ₀ a = 1)
    (g : SchwartzNPointSpace d n) :
    diffVarReduction d n (sectionOf d n φ₀ g) = g := by
  ext ξ
  change
    ∫ a : Fin (d + 1) → ℝ,
      sectionOf d n φ₀ g (fun k μ => a μ + diffVarSection d n ξ k μ) = g ξ
  calc
    ∫ a : Fin (d + 1) → ℝ,
        sectionOf d n φ₀ g (fun k μ => a μ + diffVarSection d n ξ k μ)
      = ∫ a : Fin (d + 1) → ℝ, φ₀ a * g ξ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with a
          show (φ₀.prependField g)
              (basepointDiffCLE d n (fun k μ => a μ + diffVarSection d n ξ k μ)) = φ₀ a * g ξ
          have key : basepointDiffCLE d n (fun k μ => a μ + diffVarSection d n ξ k μ) =
              Fin.cons a ξ := by
            funext k μ; refine Fin.cases ?_ ?_ k
            · simp [diffVarSection_zero]
            · intro i
              simp only [basepointDiffCLE_apply_succ, Fin.cons_succ, diffVarSection_succ]
              ring
          simp [key, SchwartzMap.prependField_apply, Fin.cons_zero, Fin.cons_succ]
    _ = (∫ a : Fin (d + 1) → ℝ, φ₀ a) * g ξ := by
          trans g ξ • ∫ a : Fin (d + 1) → ℝ, (φ₀ a : ℂ)
          · rw [← integral_smul]
            congr 1; funext a; rw [smul_eq_mul, mul_comm]
          · rw [smul_eq_mul, mul_comm]
    _ = g ξ := by rw [hφ₀]; ring

private theorem eq_of_splitFirst_eq_splitLast_eq_local {p q : ℕ}
    {x y : Fin (p + q) → ℝ}
    (hfirst : splitFirst p q x = splitFirst p q y)
    (hlast : splitLast p q x = splitLast p q y) :
    x = y := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    exact congrFun hfirst a
  · intro b
    exact congrFun hlast b

private theorem splitFirst_smul_local {p q : ℕ} (r : ℝ)
    (x : Fin (p + q) → ℝ) :
    splitFirst p q (r • x) = r • splitFirst p q x := by
  ext i
  simp [splitFirst, Pi.smul_apply]

private theorem splitLast_smul_local {p q : ℕ} (r : ℝ)
    (x : Fin (p + q) → ℝ) :
    splitLast p q (r • x) = r • splitLast p q x := by
  ext i
  simp [splitLast, Pi.smul_apply]

@[simp] private theorem castFinCLE_apply_local {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) := rfl

private noncomputable def basepointDiffPairCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d (n + 1) ≃L[ℝ] (BasepointSpace d × NPointSpacetime d n) where
  toFun x := (x 0, fun k μ => x k.succ μ - x k.castSucc μ)
  invFun y k μ := y.1 μ + diffVarSection d n y.2 k μ
  left_inv := by
    intro x
    ext k μ
    refine Fin.cases ?_ ?_ k
    · simp [diffVarSection_zero]
    · intro i
      suffices h : ∀ j : Fin (n + 1),
          x 0 μ + diffVarSection d n (fun l ν => x l.succ ν - x l.castSucc ν) j μ = x j μ by
        exact h i.succ
      intro j
      induction j using Fin.induction with
      | zero =>
          simp [diffVarSection_zero]
      | succ j ih =>
          have hsucc :=
            diffVarSection_succ (d := d) n
              (fun l ν => x l.succ ν - x l.castSucc ν) j μ
          linarith
  right_inv := by
    intro y
    rcases y with ⟨a, ξ⟩
    apply Prod.ext
    · funext μ
      simp [diffVarSection_zero]
    · funext k
      funext μ
      change (a μ + diffVarSection d n ξ k.succ μ) -
          (a μ + diffVarSection d n ξ k.castSucc μ) = ξ k μ
      rw [diffVarSection_succ]
      ring
  map_add' := by
    intro x y
    apply Prod.ext
    · funext μ
      simp
    · funext k
      funext μ
      simp [add_sub_add_comm]
  map_smul' := by
    intro c x
    apply Prod.ext
    · funext μ
      simp
    · funext k
      funext μ
      change c * x k.succ μ - c * x k.castSucc μ = c * (x k.succ μ - x k.castSucc μ)
      ring
  continuous_toFun := by
    exact Continuous.prodMk (continuous_apply 0) <| by
      apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      exact (continuous_apply_apply k.succ μ).sub (continuous_apply_apply k.castSucc μ)
  continuous_invFun := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro μ
    apply Continuous.add
    · exact (continuous_apply μ).comp continuous_fst
    · exact (continuous_apply μ).comp
        ((continuous_apply k).comp
          ((diffVarSection d n).continuous.comp continuous_snd))

@[simp] private lemma basepointDiffPairCLE_apply
    (d : ℕ) (n : ℕ) (x : NPointSpacetime d (n + 1)) :
    basepointDiffPairCLE d n x =
      (x 0, fun k μ => x k.succ μ - x k.castSucc μ) := rfl

@[simp] private lemma basepointDiffPairCLE_translate_diagonal
    (d : ℕ) (n : ℕ) (a : BasepointSpace d) (x : NPointSpacetime d (n + 1)) :
    basepointDiffPairCLE d n (fun i μ => x i μ + a μ) =
      ((basepointDiffPairCLE d n x).1 + a, (basepointDiffPairCLE d n x).2) := by
  apply Prod.ext
  · funext μ
    simp [basepointDiffPairCLE]
  · funext k
    funext μ
    simp [basepointDiffPairCLE, add_sub_add_right_eq_sub]

private noncomputable def flattenDiffCLE (d : ℕ) (n : ℕ) :
    NPointSpacetime d n ≃L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
  (({ (Equiv.curry (Fin n) (Fin (d + 1)) ℝ).symm with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } :
      (Fin n → Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin n × Fin (d + 1) → ℝ)).trans
    (LinearEquiv.funCongrLeft ℝ ℝ finProdFinEquiv.symm)).toContinuousLinearEquiv

@[simp] private lemma flattenDiffCLE_symm_apply
    (d : ℕ) (n : ℕ) (u : Fin (n * (d + 1)) → ℝ) (i : Fin n) (j : Fin (d + 1)) :
    (flattenDiffCLE d n).symm u i j = u (finProdFinEquiv (i, j)) := rfl

private noncomputable def flattenBasepointDiffCLE (d : ℕ) (n : ℕ) :
    (BasepointSpace d × NPointSpacetime d n) ≃L[ℝ]
      (Fin ((d + 1) + n * (d + 1)) → ℝ) :=
  (({ toFun := fun y =>
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) y.1 +
          zeroHeadBlockShift (m := d + 1) (n := n * (d + 1))
            (flattenDiffCLE d n y.2)
      invFun := fun u =>
        (splitFirst (d + 1) (n * (d + 1)) u,
          (flattenDiffCLE d n).symm (splitLast (d + 1) (n * (d + 1)) u))
      left_inv := by
        intro y
        rcases y with ⟨a, ξ⟩
        apply Prod.ext
        · funext μ
          simp
        · apply (flattenDiffCLE d n).injective
          funext i
          simp
      right_inv := by
        intro u
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp
        · simp
      map_add' := by
        intro y z
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp [map_add]
        · simp [map_add]
      map_smul' := by
        intro r y
        apply eq_of_splitFirst_eq_splitLast_eq_local
        · simp [splitFirst_smul_local, map_smul]
        · simp [splitLast_smul_local, map_smul] } :
      (BasepointSpace d × NPointSpacetime d n) ≃ₗ[ℝ]
        (Fin ((d + 1) + n * (d + 1)) → ℝ))).toContinuousLinearEquiv

@[simp] private lemma flattenBasepointDiffCLE_add_basepoint
    (d : ℕ) (n : ℕ) (a₀ : BasepointSpace d)
    (y : BasepointSpace d × NPointSpacetime d n) :
    flattenBasepointDiffCLE d n (y.1 + a₀, y.2) =
      flattenBasepointDiffCLE d n y +
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) a₀ := by
  rcases y with ⟨a, ξ⟩
  apply eq_of_splitFirst_eq_splitLast_eq_local
  · ext i
    simp [flattenBasepointDiffCLE, splitFirst_add, add_assoc, add_left_comm, add_comm]
  · ext i
    simp [flattenBasepointDiffCLE, splitLast_add, add_assoc, add_left_comm, add_comm]

private noncomputable def flattenBasepointDiffSchwartz (d : ℕ) (n : ℕ) :
    SchwartzNPointSpace d (n + 1) →L[ℂ]
      SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (flattenBasepointDiffCLE d n).symm).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (basepointDiffPairCLE d n).symm)

@[simp] private lemma flattenBasepointDiffSchwartz_apply
    (d : ℕ) (n : ℕ) (f : SchwartzNPointSpace d (n + 1))
    (u : Fin ((d + 1) + n * (d + 1)) → ℝ) :
    flattenBasepointDiffSchwartz d n f u =
      f ((basepointDiffPairCLE d n).symm ((flattenBasepointDiffCLE d n).symm u)) := by
  simp [flattenBasepointDiffSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

private noncomputable def unflattenBasepointDiffSchwartz (d : ℕ) (n : ℕ) :
    SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzNPointSpace d (n + 1) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (basepointDiffPairCLE d n)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (flattenBasepointDiffCLE d n))

@[simp] private lemma unflatten_flattenBasepointDiffSchwartz
    (d : ℕ) (n : ℕ) (f : SchwartzNPointSpace d (n + 1)) :
    unflattenBasepointDiffSchwartz d n (flattenBasepointDiffSchwartz d n f) = f := by
  ext x
  simpa [unflattenBasepointDiffSchwartz, flattenBasepointDiffSchwartz, basepointDiffPairCLE] using
    congrArg f ((basepointDiffPairCLE d n).symm_apply_apply x)

private noncomputable def transportedWHeadBlockCLM
    (d : ℕ) (n : ℕ)
    (W : SchwartzNPointSpace d (n + 1) → ℂ)
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W) :
    SchwartzMap (Fin ((d + 1) + n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
  { toFun := fun ψ => W (unflattenBasepointDiffSchwartz d n ψ)
    map_add' := by
      intro ψ χ
      simp [unflattenBasepointDiffSchwartz, hW_lin.map_add]
    map_smul' := by
      intro c ψ
      simp [unflattenBasepointDiffSchwartz, hW_lin.map_smul]
    cont := hW_cont.comp (unflattenBasepointDiffSchwartz d n).continuous }

private lemma transportedWHeadBlockInvariant
    (d : ℕ) [NeZero d] (n : ℕ)
    {W : SchwartzNPointSpace d (n + 1) → ℂ}
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W)
    (hW_transl : ∀ (a : BasepointSpace d)
      (f g : SchwartzNPointSpace d (n + 1)),
      (∀ x : NPointSpacetime d (n + 1),
        g.toFun x = f.toFun (fun i => x i + a)) →
      W f = W g) :
    IsHeadBlockTranslationInvariantSchwartzCLM
      (m := d + 1) (n := n * (d + 1))
      (transportedWHeadBlockCLM d n W hW_cont hW_lin) := by
  intro a
  ext ψ
  symm
  refine hW_transl a _ _ ?_
  intro x
  change ψ
      (flattenBasepointDiffCLE d n (basepointDiffPairCLE d n x) +
        zeroTailBlockShift (m := d + 1) (n := n * (d + 1)) a) =
    ψ (flattenBasepointDiffCLE d n
      (basepointDiffPairCLE d n (fun i μ => x i μ + a μ)))
  rw [basepointDiffPairCLE_translate_diagonal, flattenBasepointDiffCLE_add_basepoint]

private def basepointAssemble (d : ℕ) (m : ℕ) (hm : m ≤ d + 1) :
    (Fin m → ℝ) → (Fin (d + 1 - m) → ℝ) → (Fin (d + 1) → ℝ) :=
  fun aHead aTail =>
    castFinCLE (Nat.add_sub_of_le hm)
      (fun i : Fin (m + (d + 1 - m)) =>
        Fin.addCases (fun j => aHead (Fin.rev j)) aTail i)

@[simp] private lemma basepointAssemble_zero
    (d : ℕ) (aTail : Fin (d + 1) → ℝ) :
    basepointAssemble d 0 (Nat.zero_le (d + 1)) default aTail = aTail := by
  ext i
  rw [basepointAssemble, castFinCLE_apply_local]
  have hidx :
      ((finCongr (Nat.add_sub_of_le (Nat.zero_le (d + 1)))).symm i) = Fin.natAdd 0 i := by
    apply Fin.ext
    simp [Fin.natAdd]
  rw [hidx, Fin.addCases_right]

@[simp] private lemma basepointAssemble_zero_any
    (d : ℕ) (hm : 0 ≤ d + 1) (aTail : Fin (d + 1) → ℝ) :
    basepointAssemble d 0 hm default aTail = aTail := by
  have hproof : hm = Nat.zero_le (d + 1) := Subsingleton.elim _ _
  cases hproof
  simpa using basepointAssemble_zero d aTail

private lemma basepointAssemble_cons
    (d : ℕ) (m : ℕ) (hm : m + 1 ≤ d + 1)
    (aHead : Fin m → ℝ) (aTail : Fin (d + 1 - (m + 1)) → ℝ) (t : ℝ) :
    basepointAssemble d m (by omega) aHead
      (show Fin (d + 1 - m) → ℝ from
        castFinCLE (by omega : (d + 1 - (m + 1)) + 1 = d + 1 - m) (Fin.cons t aTail)) =
      basepointAssemble d (m + 1) hm (Fin.cons t aHead) aTail := by
  have hm₀ : m ≤ d + 1 := by omega
  have h' : (d + 1 - (m + 1)) + 1 = d + 1 - m := by omega
  ext i
  -- Unfold both basepointAssemble evaluations through castFinCLE
  rw [basepointAssemble, basepointAssemble]
  simp only [castFinCLE_apply_local]
  -- Name the reindexed points
  set iL : Fin (m + (d + 1 - m)) :=
    (finCongr (Nat.add_sub_of_le hm₀)).symm i with hiL_def
  set iR : Fin ((m + 1) + (d + 1 - (m + 1))) :=
    (finCongr (Nat.add_sub_of_le hm)).symm i with hiR_def
  have hiL_val : iL.val = i.val := by simp [iL]
  have hiR_val : iR.val = i.val := by simp [iR]
  -- Case analysis on i.val
  rcases lt_or_ge i.val m with h₁ | h₁
  · -- i.val < m: both sides reduce to aHead evaluated at the reversed head index
    have hLlt : iL.val < m := hiL_val ▸ h₁
    have hRlt : iR.val < m + 1 := by rw [hiR_val]; omega
    have hL_eq : iL = Fin.castAdd (d + 1 - m) (iL.castLT hLlt) := by
      apply Fin.ext; simp
    have hR_eq : iR = Fin.castAdd (d + 1 - (m + 1)) (iR.castLT hRlt) := by
      apply Fin.ext; simp
    rw [hL_eq, Fin.addCases_left, hR_eq, Fin.addCases_left]
    -- Both head indices have the same val = i.val < m, so the right is
    -- `Fin.castSucc` of the left.
    have hcastSucc :
        (iR.castLT hRlt : Fin (m + 1)) = Fin.castSucc (iL.castLT hLlt) := by
      apply Fin.ext
      simp [hiL_val, hiR_val]
    rw [hcastSucc, Fin.rev_castSucc, Fin.cons_succ]
  · rcases eq_or_lt_of_le h₁ with h₂ | h₂
    · -- i.val = m: LHS hits the new cons head `t`; RHS hits Fin.cons t aHead 0 = t
      have hLnlt : ¬ iL.val < m := by rw [hiL_val, ← h₂]; omega
      have hRlt : iR.val < m + 1 := by rw [hiR_val, ← h₂]; omega
      have hLge : m ≤ iL.val := by rw [hiL_val, ← h₂]
      have hR_eq : iR = Fin.castAdd (d + 1 - (m + 1)) (iR.castLT hRlt) := by
        apply Fin.ext; simp
      -- LHS: use right branch of addCases with subNat-reconstruction
      have hLsub_val :
          (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)).val = 0 := by
        show iL.val - m = 0
        omega
      have hL_eq :
          iL = Fin.natAdd m
            (⟨iL.val - m, by
              have : iL.val < m + (d + 1 - m) := iL.isLt
              omega⟩ : Fin (d + 1 - m)) := by
        apply Fin.ext
        show iL.val = m + (iL.val - m)
        omega
      rw [hL_eq, Fin.addCases_right, hR_eq, Fin.addCases_left]
      -- RHS head index: val m on Fin (m + 1) → Fin.last m
      have hRlast : (iR.castLT hRlt : Fin (m + 1)) = Fin.last m := by
        apply Fin.ext
        show iR.val = m
        omega
      rw [hRlast, Fin.rev_last, Fin.cons_zero]
      -- LHS: castFinCLE h' (Fin.cons t aTail) at the subNat index (val 0) equals t
      rw [castFinCLE_apply_local]
      have h0 :
          ((finCongr h').symm (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)) : Fin ((d + 1 - (m + 1)) + 1)) = 0 := by
        apply Fin.ext
        exact hLsub_val
      rw [h0, Fin.cons_zero]
    · -- i.val > m: both sides reduce to `aTail` at the tail index i.val - (m+1)
      have hLnlt : ¬ iL.val < m := by rw [hiL_val]; omega
      have hRnlt : ¬ iR.val < m + 1 := by rw [hiR_val]; omega
      have hLge : m ≤ iL.val := by rw [hiL_val]; omega
      have hRge : m + 1 ≤ iR.val := by rw [hiR_val]; omega
      have hL_eq :
          iL = Fin.natAdd m
            (⟨iL.val - m, by
              have : iL.val < m + (d + 1 - m) := iL.isLt
              omega⟩ : Fin (d + 1 - m)) := by
        apply Fin.ext
        show iL.val = m + (iL.val - m)
        omega
      have hR_eq :
          iR = Fin.natAdd (m + 1)
            (⟨iR.val - (m + 1), by
              have : iR.val < (m + 1) + (d + 1 - (m + 1)) := iR.isLt
              omega⟩ : Fin (d + 1 - (m + 1))) := by
        apply Fin.ext
        show iR.val = (m + 1) + (iR.val - (m + 1))
        omega
      rw [hL_eq, Fin.addCases_right, hR_eq, Fin.addCases_right]
      -- LHS: castFinCLE h' (Fin.cons t aTail) at a subNat index with val > 0
      rw [castFinCLE_apply_local]
      -- Show the cast index equals Fin.succ of something, then use Fin.cons_succ
      have hsucc :
          ((finCongr h').symm (⟨iL.val - m, by
            have : iL.val < m + (d + 1 - m) := iL.isLt
            omega⟩ : Fin (d + 1 - m)) : Fin ((d + 1 - (m + 1)) + 1)) =
          Fin.succ (⟨iR.val - (m + 1), by
            have : iR.val < (m + 1) + (d + 1 - (m + 1)) := iR.isLt
            omega⟩ : Fin (d + 1 - (m + 1))) := by
        apply Fin.ext
        simp [hiL_val, hiR_val]
        omega
      rw [hsucc, Fin.cons_succ]

private lemma sliceIntegral_flattenBasepointDiff_step
    (d : ℕ) (n : ℕ) (m : ℕ)
    (hm : m + 1 ≤ d + 1)
    (f : SchwartzNPointSpace d (n + 1))
    (x : Fin (m + ((d + 1 - (m + 1)) + n * (d + 1))) → ℝ) :
    sliceIntegral
      (reindexSchwartzFin
        (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
        (reindexSchwartzFin
          (by omega : (d + 1) + n * (d + 1) =
            (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)))
          (flattenBasepointDiffSchwartz d n f))) x
      =
    ∫ t : ℝ,
      (reindexSchwartzFin
        (by omega : (d + 1) + n * (d + 1) =
          (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)))
        (flattenBasepointDiffSchwartz d n f))
        ((castFinCLE
            (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))).symm
          (Fin.cons t x)) := by
  simp [sliceIntegral_apply, sliceIntegralRaw, reindexSchwartzFin_apply]

private lemma integrateHeadBlock_slice_swap_flattenBasepoint
    {m N : ℕ}
    (F : SchwartzMap (Fin ((m + 1) + N) → ℝ) ℂ)
    (u : Fin N → ℝ) :
    integrateHeadBlock (m := m)
        (n := N)
        (sliceIntegral
          (reindexSchwartzFin (Nat.succ_add m N) F)) u =
      ∫ t : ℝ,
        integrateHeadBlock (m := m)
            (n := N + 1)
            (reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) F)
          (Fin.cons t u) := by
  induction m generalizing N u with
  | zero =>
      simp only [integrateHeadBlock, reindexSchwartzFin_apply, sliceIntegral_apply,
        sliceIntegralRaw]
      congr 1
      funext t
      apply congrArg
      ext i
      rcases i with ⟨iv, hiv⟩
      cases iv with
      | zero =>
          simp only [castFinCLE_symm_apply, Fin.cons]
          rfl
      | succ k =>
          simp only [castFinCLE_symm_apply, Fin.cons]
          rfl
  | succ m ihm =>
      -- F : SchwartzMap (Fin (((m + 1) + 1) + N) → ℝ) ℂ
      -- which equals Fin ((m + 2) + N) → ℝ by defn-eq (since (m+1)+1 = m+2 defn).
      -- Goal: integrateHeadBlock (m+1) (sliceIntegral (reindexSchwartzFin (Nat.succ_add (m+1) N) F)) u = ...
      -- Unfold integrateHeadBlock (m+1) on LHS via its recursive definition.
      let G :
          SchwartzMap (Fin ((m + 1) + N) → ℝ) ℂ :=
        sliceIntegral (reindexSchwartzFin (Nat.succ_add (m + 1) N) F)
      let F' :
          SchwartzMap (Fin ((m + 1) + (N + 1)) → ℝ) ℂ :=
        reindexSchwartzFin (by omega : ((m + 1) + 1) + N = (m + 1) + (N + 1)) F
      have hG_reindex :
          reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) G =
          sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F') := by
        ext x
        simp only [G, F', reindexSchwartzFin_apply, sliceIntegral_apply, sliceIntegralRaw]
        congr 1
        funext t
        apply congrArg
        ext i
        rcases i with ⟨iv, hiv⟩
        cases iv with
        | zero =>
            simp only [castFinCLE_symm_apply, Fin.cons]
            rfl
        | succ k =>
            simp only [castFinCLE_symm_apply, Fin.cons]
            rfl
      calc
        integrateHeadBlock (m := m + 1) (n := N)
            (sliceIntegral (reindexSchwartzFin (Nat.succ_add (m + 1) N) F)) u
          =
            integrateHeadBlock (m := m) (n := N)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add m N) G)) u := by
                simp [integrateHeadBlock, G]
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m) (n := N + 1)
                (reindexSchwartzFin (by omega : (m + 1) + N = m + (N + 1)) G)
                (Fin.cons s u) := by
                  exact ihm (N := N) (u := u) (F := G)
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m) (n := N + 1)
                (sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F'))
                (Fin.cons s u) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  rw [hG_reindex]
        _ =
            ∫ s : ℝ, ∫ t : ℝ,
              integrateHeadBlock (m := m) (n := (N + 1) + 1)
                (reindexSchwartzFin (by omega : (m + 1) + (N + 1) = m + ((N + 1) + 1)) F')
                (Fin.cons t (Fin.cons s u)) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  exact ihm (N := N + 1) (u := Fin.cons s u) (F := F')
        _ =
            ∫ s : ℝ,
              integrateHeadBlock (m := m + 1) (n := N + 1)
                (reindexSchwartzFin
                  (by omega : ((m + 1) + 1) + N = (m + 1) + (N + 1)) F)
                (Fin.cons s u) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  symm
                  show integrateHeadBlock (m := m + 1) (n := N + 1) F' (Fin.cons s u) = _
                  show integrateHeadBlock (m := m) (n := N + 1)
                      (sliceIntegral (reindexSchwartzFin (Nat.succ_add m (N + 1)) F'))
                      (Fin.cons s u) = _
                  exact ihm (N := N + 1) (u := Fin.cons s u) (F := F')

private lemma integrateHeadBlock_flattenBasepointDiff_aux_m
    (d : ℕ) [NeZero d] (n : ℕ)
    (m : ℕ) (hm : m ≤ d + 1)
    (f : SchwartzNPointSpace d (n + 1))
    (u : Fin ((d + 1 - m) + n * (d + 1)) → ℝ) :
    integrateHeadBlock (m := m) (n := (d + 1 - m) + n * (d + 1))
      (reindexSchwartzFin (by omega)
        (flattenBasepointDiffSchwartz d n f)) u =
    ∫ aHead : Fin m → ℝ,
      f (fun k μ =>
        (basepointAssemble d m hm aHead
          (splitFirst (d + 1 - m) (n * (d + 1)) u)) μ +
        diffVarSection d n
          ((flattenDiffCLE d n).symm
            (splitLast (d + 1 - m) (n * (d + 1)) u)) k μ) := by
  induction m with
  | zero =>
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      have hu :
          ((castFinCLE
              (by omega : (d + 1) + n * (d + 1) =
                0 + (d + 1 - 0 + n * (d + 1)))).symm
            ((castFinCLE (Nat.zero_add (d + 1 - 0 + n * (d + 1)))).symm u)) = u := by
        ext i
        simp [castFinCLE_symm_apply]
      rw [integrateHeadBlock, hvol, MeasureTheory.integral_dirac]
      rw [reindexSchwartzFin_apply]
      rw [reindexSchwartzFin_apply]
      rw [flattenBasepointDiffSchwartz_apply]
      rw [hu]
      have hA :
          basepointAssemble d 0 hm default
            (splitFirst (d + 1 - 0) (n * (d + 1)) u) =
          splitFirst (d + 1 - 0) (n * (d + 1)) u := by
        simpa using
          basepointAssemble_zero_any d hm
            (splitFirst (d + 1 - 0) (n * (d + 1)) u)
      congr 1
      ext k μ
      rw [hA]
      change ((flattenBasepointDiffCLE d n).symm u).1 μ +
          diffVarSection d n (((flattenBasepointDiffCLE d n).symm u).2) k μ =
        splitFirst (d + 1) (n * (d + 1)) u μ +
          diffVarSection d n
            ((flattenDiffCLE d n).symm (splitLast (d + 1) (n * (d + 1)) u)) k μ
      simp [flattenBasepointDiffCLE]
  | succ m ihm =>
      have hm' : m + 1 ≤ d + 1 := hm
      have hmle : m ≤ d + 1 := by omega
      have hdiff : (d + 1 - m) = (d + 1 - (m + 1)) + 1 := by omega
      have hcastEq : (d + 1 - m) + n * (d + 1) =
          ((d + 1 - (m + 1)) + n * (d + 1)) + 1 := by omega
      have hRindex : (d + 1) + n * (d + 1) =
          (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) := by omega
      have hRindex' : (d + 1) + n * (d + 1) =
          m + ((d + 1 - m) + n * (d + 1)) := by omega
      rw [integrateHeadBlock]
      have hswap :
          integrateHeadBlock (m := m)
              (n := (d + 1 - (m + 1)) + n * (d + 1))
              (sliceIntegral
                (reindexSchwartzFin
                  (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
                  (reindexSchwartzFin hRindex
                    (flattenBasepointDiffSchwartz d n f)))) u =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := (d + 1 - m) + n * (d + 1))
                  (reindexSchwartzFin hRindex'
                    (flattenBasepointDiffSchwartz d n f))
                ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
        have hswap0 :=
          integrateHeadBlock_slice_swap_flattenBasepoint
            (F := reindexSchwartzFin hRindex (flattenBasepointDiffSchwartz d n f))
            (u := u)
        have hreindex :
            reindexSchwartzFin
                (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                  m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                (reindexSchwartzFin hRindex
                  (flattenBasepointDiffSchwartz d n f)) =
              reindexSchwartzFin
                (by omega : m + (d + 1 - m + n * (d + 1)) =
                  m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                (reindexSchwartzFin hRindex'
                  (flattenBasepointDiffSchwartz d n f)) := by
          ext x
          rw [reindexSchwartzFin_apply, reindexSchwartzFin_apply,
            reindexSchwartzFin_apply, reindexSchwartzFin_apply]
          rw [flattenBasepointDiffSchwartz_apply, flattenBasepointDiffSchwartz_apply]
          congr 1
        calc
          integrateHeadBlock (m := m)
              (n := (d + 1 - (m + 1)) + n * (d + 1))
              (sliceIntegral
                (reindexSchwartzFin
                  (Nat.succ_add m ((d + 1 - (m + 1)) + n * (d + 1)))
                  (reindexSchwartzFin hRindex
                    (flattenBasepointDiffSchwartz d n f)))) u
              =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := ((d + 1 - (m + 1)) + n * (d + 1)) + 1)
                  (reindexSchwartzFin
                    (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                      m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                    (reindexSchwartzFin hRindex
                      (flattenBasepointDiffSchwartz d n f)))
                  (Fin.cons t u) := by
                    exact hswap0
          _ =
            ∫ t : ℝ,
              integrateHeadBlock (m := m)
                  (n := (d + 1 - m) + n * (d + 1))
                  (reindexSchwartzFin hRindex'
                    (flattenBasepointDiffSchwartz d n f))
                  ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with t
                    have hG :
                        integrateHeadBlock (m := m)
                            (n := ((d + 1 - (m + 1)) + n * (d + 1)) + 1)
                            (reindexSchwartzFin
                              (by omega : (m + 1) + ((d + 1 - (m + 1)) + n * (d + 1)) =
                                m + (((d + 1 - (m + 1)) + n * (d + 1)) + 1))
                              (reindexSchwartzFin hRindex
                                (flattenBasepointDiffSchwartz d n f)))
                            (Fin.cons t u)
                          =
                        integrateHeadBlock (m := m)
                            (n := (d + 1 - m) + n * (d + 1))
                            (reindexSchwartzFin hRindex'
                              (flattenBasepointDiffSchwartz d n f))
                            ((castFinCLE hcastEq).symm (Fin.cons t u)) := by
                      rw [hreindex]
                      have hnat : ∀ (p : ℕ) (a b : ℕ) (hab : a = b)
                          (h : p + a = p + b)
                          (F : SchwartzMap (Fin (p + a) → ℝ) ℂ) (y : Fin b → ℝ),
                          integrateHeadBlock (m := p) (n := b)
                              (reindexSchwartzFin h F) y =
                            integrateHeadBlock (m := p) (n := a) F
                              ((castFinCLE hab).symm y) := by
                        intro p
                        induction p with
                        | zero =>
                            intro a b hab h F y
                            simp only [integrateHeadBlock, reindexSchwartzFin_apply]
                            apply congrArg F
                            ext i
                            simp only [castFinCLE_symm_apply]
                            apply congrArg y
                            apply Fin.ext
                            rfl
                        | succ k ihk =>
                            intro a b hab h F y
                            show integrateHeadBlock (m := k) (n := b)
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k b)
                                      (reindexSchwartzFin h F))) y =
                                integrateHeadBlock (m := k) (n := a)
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k a) F))
                                  ((castFinCLE hab).symm y)
                            have h' : k + a = k + b := by omega
                            have hs :
                                sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k b)
                                      (reindexSchwartzFin h F))
                                  =
                                reindexSchwartzFin h'
                                  (sliceIntegral
                                    (reindexSchwartzFin (Nat.succ_add k a) F)) := by
                              apply SchwartzMap.ext
                              intro z
                              simp only [reindexSchwartzFin_apply, sliceIntegral_apply,
                                sliceIntegralRaw]
                              congr 1
                              funext tt
                              apply congrArg F
                              ext i
                              rcases i with ⟨iv, hiv⟩
                              cases iv with
                              | zero =>
                                  simp only [castFinCLE_symm_apply, Fin.cons]
                                  rfl
                              | succ iv' =>
                                  simp only [castFinCLE_symm_apply, Fin.cons]
                                  rfl
                            rw [hs]
                            exact ihk a b hab h' _ y
                      exact hnat m _ _ hcastEq _ _ (Fin.cons t u)
                    exact hG
      rw [hswap]
      simp_rw [ihm hmle]
      have hSF : ∀ t : ℝ,
          splitFirst (d + 1 - m) (n * (d + 1))
            ((castFinCLE hcastEq).symm (Fin.cons t u)) =
          (castFinCLE hdiff).symm
            (Fin.cons t (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) := by
        intro t
        ext i
        simp only [splitFirst, castFinCLE_symm_apply]
        rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
        · have hL_zero :
              (finCongr hcastEq) (Fin.castAdd (n * (d + 1)) i) =
                (0 : Fin (d + 1 - (m + 1) + n * (d + 1) + 1)) := by
            apply Fin.ext
            simp [Fin.val_castAdd, hi0]
          have hR_zero :
              (finCongr hdiff) i = (0 : Fin (d + 1 - (m + 1) + 1)) := by
            apply Fin.ext
            simp [hi0]
          rw [hL_zero, hR_zero, Fin.cons_zero, Fin.cons_zero]
        · have hipred : i.val - 1 < d + 1 - (m + 1) := by
            have := i.isLt; omega
          have hipred' : i.val - 1 < d + 1 - (m + 1) + n * (d + 1) := by
            have := i.isLt; omega
          have hL_succ :
              (finCongr hcastEq) (Fin.castAdd (n * (d + 1)) i) =
                Fin.succ ⟨i.val - 1, hipred'⟩ := by
            apply Fin.ext
            simp [Fin.val_castAdd, Fin.val_succ]
            omega
          have hR_succ :
              (finCongr hdiff) i = Fin.succ ⟨i.val - 1, hipred⟩ := by
            apply Fin.ext
            simp [Fin.val_succ]
            omega
          rw [hL_succ, hR_succ, Fin.cons_succ, Fin.cons_succ]
          rfl
      have hSL : ∀ t : ℝ,
          splitLast (d + 1 - m) (n * (d + 1))
            ((castFinCLE hcastEq).symm (Fin.cons t u)) =
          splitLast (d + 1 - (m + 1)) (n * (d + 1)) u := by
        intro t
        ext j
        simp only [splitLast, castFinCLE_symm_apply]
        have hjpos :
            0 < ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val := by
          simp [Fin.val_natAdd]
          omega
        have hj_pred_lt :
            ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val - 1 <
              d + 1 - (m + 1) + n * (d + 1) := by
          have := ((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).isLt
          omega
        have hj_succ :
            (finCongr hcastEq) (Fin.natAdd (d + 1 - m) j) =
              Fin.succ ⟨((finCongr hcastEq) (Fin.natAdd (d + 1 - m) j)).val - 1,
                hj_pred_lt⟩ := by
          apply Fin.ext
          simp [Fin.val_succ]
          omega
        rw [hj_succ, Fin.cons_succ]
        apply congrArg u
        apply Fin.ext
        simp [Fin.val_natAdd]
        omega
      simp_rw [hSF, hSL]
      have happend :
          ∀ (t : ℝ) (aHead : Fin m → ℝ),
            basepointAssemble d m hmle aHead
              ((castFinCLE hdiff).symm
                (Fin.cons t
                  (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u))) =
              basepointAssemble d (m + 1) hm' (Fin.cons t aHead)
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) := by
        intro t aHead
        change basepointAssemble d m hmle aHead
            (castFinCLE hdiff.symm
              (Fin.cons t (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u))) = _
        exact basepointAssemble_cons (d := d) (m := m) (hm := hm')
          (aHead := aHead)
          (aTail := splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) t
      simp_rw [happend]
      have hFubini :
          (∫ z : ℝ × (Fin m → ℝ),
            f (fun k μ =>
              (basepointAssemble d (m + 1) hm' (Fin.cons z.1 z.2)
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
              diffVarSection d n
                ((flattenDiffCLE d n).symm
                  (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ)
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.Measure.pi fun _ : Fin m =>
                (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) =
          ∫ a : Fin (m + 1) → ℝ,
            f (fun k μ =>
              (basepointAssemble d (m + 1) hm' a
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
              diffVarSection d n
                ((flattenDiffCLE d n).symm
                  (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ) := by
        rw [MeasureTheory.volume_pi]
        exact OSReconstruction.integral_finSucc_cons_eq
          (f := fun a : Fin (m + 1) → ℝ =>
            f (fun k μ =>
              (basepointAssemble d (m + 1) hm' a
                (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
              diffVarSection d n
                ((flattenDiffCLE d n).symm
                  (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ))
      -- Use Fubini: the integrand (as a function of z = (t, aHead)) is integrable because
      -- it equals a Schwartz function composed with an affine transformation, hence rapidly
      -- decaying in both variables. Apply `MeasureTheory.integral_prod` + `hFubini`.
      have hint :
          MeasureTheory.Integrable
            (fun z : ℝ × (Fin m → ℝ) =>
              f (fun k μ =>
                (basepointAssemble d (m + 1) hm' (Fin.cons z.1 z.2)
                  (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)) μ +
                diffVarSection d n
                  ((flattenDiffCLE d n).symm
                    (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)) k μ))
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
              (MeasureTheory.Measure.pi fun _ : Fin m =>
                (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
        -- Define the affine map `g : (Fin (m+1) → ℝ) → NPointSpacetime d (n+1)`
        -- whose composition with f gives the integrand.
        let gBase : (Fin (m + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun a =>
          basepointAssemble d (m + 1) hm' a
            (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)
        let gDiff : NPointSpacetime d n :=
          (flattenDiffCLE d n).symm
            (splitLast (d + 1 - (m + 1)) (n * (d + 1)) u)
        let g : (Fin (m + 1) → ℝ) → NPointSpacetime d (n + 1) := fun a =>
          (basepointDiffPairCLE d n).symm (gBase a, gDiff)
        -- Linear part of `gBase`: a ↦ basepointAssemble d (m+1) hm' a 0.
        let L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
          { toFun := fun a => basepointAssemble d (m + 1) hm' a
              (0 : Fin (d + 1 - (m + 1)) → ℝ)
            map_add' := by
              intro a a'
              ext i
              simp only [basepointAssemble, castFinCLE_apply_local, Pi.add_apply]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i
              induction j using Fin.addCases with
              | left k => simp
              | right k => simp
            map_smul' := by
              intro r a
              ext i
              simp only [basepointAssemble, castFinCLE_apply_local, Pi.smul_apply,
                RingHom.id_apply, smul_eq_mul]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i
              induction j using Fin.addCases with
              | left k => simp
              | right k => simp
            cont := by
              apply continuous_pi
              intro i
              simp only [basepointAssemble, castFinCLE_apply_local]
              set j := (finCongr (Nat.add_sub_of_le hm')).symm i with hj
              clear_value j
              induction j using Fin.addCases with
              | left k =>
                  simp only [Fin.addCases_left]
                  exact continuous_apply _
              | right k =>
                  simp only [Fin.addCases_right]
                  exact continuous_const }
        let cBase : Fin (d + 1) → ℝ :=
          basepointAssemble d (m + 1) hm' (0 : Fin (m + 1) → ℝ)
            (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u)
        have hgBase_eq : ∀ a, gBase a = L a + cBase := by
          intro a
          ext i
          change basepointAssemble d (m + 1) hm' a
              (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) i =
            basepointAssemble d (m + 1) hm' a
              (0 : Fin (d + 1 - (m + 1)) → ℝ) i +
            basepointAssemble d (m + 1) hm' (0 : Fin (m + 1) → ℝ)
              (splitFirst (d + 1 - (m + 1)) (n * (d + 1)) u) i
          simp only [basepointAssemble, castFinCLE_apply_local]
          set j := (finCongr (Nat.add_sub_of_le hm')).symm i
          induction j using Fin.addCases with
          | left k => simp
          | right k => simp
        have hgBase_temp : Function.HasTemperateGrowth gBase := by
          have hL_temp := L.hasTemperateGrowth
          have hcBase_temp :
              Function.HasTemperateGrowth (fun _ : Fin (m + 1) → ℝ => cBase) :=
            Function.HasTemperateGrowth.const cBase
          have hsum :
              Function.HasTemperateGrowth (fun a => L a + cBase) :=
            hL_temp.add hcBase_temp
          have heq : (fun a => L a + cBase) = gBase := by
            funext a
            exact (hgBase_eq a).symm
          rwa [heq] at hsum
        -- K : CLM y ↦ CLE.symm (y, 0)
        let K : (Fin (d + 1) → ℝ) →L[ℝ] NPointSpacetime d (n + 1) :=
          (basepointDiffPairCLE d n).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.inl ℝ (Fin (d + 1) → ℝ) (NPointSpacetime d n))
        let c_g : NPointSpacetime d (n + 1) :=
          (basepointDiffPairCLE d n).symm ((0 : Fin (d + 1) → ℝ), gDiff)
        have hg_eq : ∀ a, g a = K (gBase a) + c_g := by
          intro a
          show (basepointDiffPairCLE d n).symm (gBase a, gDiff) =
              (basepointDiffPairCLE d n).symm (gBase a, (0 : NPointSpacetime d n)) +
              (basepointDiffPairCLE d n).symm ((0 : Fin (d + 1) → ℝ), gDiff)
          rw [← ContinuousLinearEquiv.map_add]
          congr 1
          simp
        have hg_temp : Function.HasTemperateGrowth g := by
          have hK_temp := K.hasTemperateGrowth
          have hK_comp :
              Function.HasTemperateGrowth (fun a => K (gBase a)) :=
            hK_temp.comp hgBase_temp
          have hc_g_temp :
              Function.HasTemperateGrowth (fun _ : Fin (m + 1) → ℝ => c_g) :=
            Function.HasTemperateGrowth.const c_g
          have hsum :
              Function.HasTemperateGrowth (fun a => K (gBase a) + c_g) :=
            hK_comp.add hc_g_temp
          have heq : (fun a => K (gBase a) + c_g) = g := by
            funext a
            exact (hg_eq a).symm
          rwa [heq] at hsum
        -- Upper bound: ‖a‖ ≤ ‖g a‖ ≤ 1 * (1 + ‖g a‖)^1
        have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ a, ‖a‖ ≤ C * (1 + ‖g a‖) ^ k := by
          refine ⟨1, 1, ?_⟩
          intro a
          -- Step 1: ‖a‖ ≤ ‖gBase a‖  (each coord of a appears in gBase a)
          have hhead : ‖a‖ ≤ ‖gBase a‖ := by
            rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
            intro i
            have hμ_eq : gBase a
                ((finCongr (Nat.add_sub_of_le hm'))
                  (Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i))) = a i := by
              simp only [gBase, basepointAssemble, castFinCLE_apply_local]
              have hj_eq :
                  (finCongr (Nat.add_sub_of_le hm')).symm
                    ((finCongr (Nat.add_sub_of_le hm'))
                      (Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i))) =
                    Fin.castAdd (d + 1 - (m + 1)) (Fin.rev i) := by
                simp
              rw [hj_eq, Fin.addCases_left, Fin.rev_rev]
            rw [← hμ_eq]
            exact norm_le_pi_norm (gBase a) _
          -- Step 2: g a 0 = gBase a, so ‖gBase a‖ = ‖g a 0‖
          have hg0 : g a 0 = gBase a := by
            ext μ
            show (gBase a) μ + diffVarSection d n gDiff 0 μ = gBase a μ
            rw [diffVarSection_zero]
            simp
          have h0 : ‖gBase a‖ ≤ ‖g a 0‖ := by rw [hg0]
          have h1 : ‖g a 0‖ ≤ ‖g a‖ := norm_le_pi_norm (g a) 0
          calc
            ‖a‖ ≤ ‖gBase a‖ := hhead
            _ ≤ ‖g a 0‖ := h0
            _ ≤ ‖g a‖ := h1
            _ ≤ 1 * (1 + ‖g a‖) ^ (1 : ℕ) := by
                simp [pow_one]
        -- Build G := f ∘ g as Schwartz map.
        let G : SchwartzMap (Fin (m + 1) → ℝ) ℂ :=
          SchwartzMap.compCLM ℂ (g := g) hg_temp hg_upper f
        have hG_apply : ∀ a, G a = f (g a) := by
          intro a
          rfl
        -- G is integrable on (Fin (m+1) → ℝ).
        have hG_int :
            MeasureTheory.Integrable
              (fun a : Fin (m + 1) → ℝ => G a)
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ)) := by
          simpa using
            (SchwartzMap.integrable
              (μ := (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ))) G)
        -- Transfer via piFinSuccAbove to ℝ × (Fin m → ℝ).
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hmp :
            MeasureTheory.MeasurePreserving e
              (MeasureTheory.volume :
                MeasureTheory.Measure (Fin (m + 1) → ℝ))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.volume :
                  MeasureTheory.Measure (Fin m → ℝ))) := by
          simpa only [e, MeasureTheory.Measure.volume_eq_prod ℝ (Fin m → ℝ)] using
            (MeasureTheory.volume_preserving_piFinSuccAbove
              (fun _ : Fin (m + 1) => ℝ) 0)
        have hpair_int :
            MeasureTheory.Integrable
              (fun p : ℝ × (Fin m → ℝ) => G (Fin.cons p.1 p.2))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.volume :
                  MeasureTheory.Measure (Fin m → ℝ))) := by
          have hiff :=
            hmp.symm.integrable_comp_emb e.symm.measurableEmbedding
              (g := fun a : Fin (m + 1) → ℝ => G a)
          refine (hiff.2 hG_int).congr ?_
          filter_upwards with p
          simp [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
        -- The target measure Measure.pi equals volume on Fin m → ℝ.
        have hint0 :
            MeasureTheory.Integrable
              (fun p : ℝ × (Fin m → ℝ) => G (Fin.cons p.1 p.2))
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
                (MeasureTheory.Measure.pi fun _ : Fin m =>
                  (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := hpair_int
        -- Congr to the actual integrand.
        refine hint0.congr ?_
        refine Filter.Eventually.of_forall ?_
        intro z
        show G (Fin.cons z.1 z.2) = _
        rw [hG_apply]
        show f (g (Fin.cons z.1 z.2)) = _
        rfl
      have integ := MeasureTheory.integral_prod _ hint
      exact integ.symm.trans hFubini

private lemma integrateHeadBlock_flattenBasepointDiff_aux
    (d : ℕ) [NeZero d] (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1))
    (u : Fin (n * (d + 1)) → ℝ) :
    integrateHeadBlock (m := d + 1) (n := n * (d + 1))
      (flattenBasepointDiffSchwartz d n f) u =
    ∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n ((flattenDiffCLE d n).symm u) k μ) := by
  have hm : d + 1 ≤ d + 1 := le_refl _
  have hab_eq : n * (d + 1) = (d + 1 - (d + 1)) + n * (d + 1) := by omega
  have hreix : (d + 1) + n * (d + 1) =
      (d + 1) + ((d + 1 - (d + 1)) + n * (d + 1)) := by omega
  -- Cast u up to aux_m's shape.
  let u' : Fin ((d + 1 - (d + 1)) + n * (d + 1)) → ℝ := castFinCLE hab_eq u
  -- Inline naturality for integrateHeadBlock w.r.t. tail reindex.
  have hnat_m : ∀ (p : ℕ) (a b : ℕ) (hab0 : a = b) (h : p + a = p + b)
      (F : SchwartzMap (Fin (p + a) → ℝ) ℂ) (y : Fin b → ℝ),
      integrateHeadBlock (m := p) (n := b) (reindexSchwartzFin h F) y =
        integrateHeadBlock (m := p) (n := a) F ((castFinCLE hab0).symm y) := by
    intro p
    induction p with
    | zero =>
        intro a b hab0 h F y
        simp only [integrateHeadBlock, reindexSchwartzFin_apply]
        apply congrArg F
        ext i
        simp only [castFinCLE_symm_apply]
        apply congrArg y
        apply Fin.ext
        rfl
    | succ k ihk =>
        intro a b hab0 h F y
        show integrateHeadBlock (m := k) (n := b)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k b)
                (reindexSchwartzFin h F))) y =
            integrateHeadBlock (m := k) (n := a)
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k a) F))
              ((castFinCLE hab0).symm y)
        have h' : k + a = k + b := by omega
        have hs :
            sliceIntegral (reindexSchwartzFin (Nat.succ_add k b)
              (reindexSchwartzFin h F)) =
            reindexSchwartzFin h'
              (sliceIntegral (reindexSchwartzFin (Nat.succ_add k a) F)) := by
          apply SchwartzMap.ext
          intro z
          simp only [reindexSchwartzFin_apply, sliceIntegral_apply, sliceIntegralRaw]
          congr 1
          funext tt
          apply congrArg F
          ext i
          rcases i with ⟨iv, hiv⟩
          cases iv with
          | zero =>
              simp only [castFinCLE_symm_apply, Fin.cons]
              rfl
          | succ iv' =>
              simp only [castFinCLE_symm_apply, Fin.cons]
              rfl
        rw [hs]
        exact ihk a b hab0 h' _ y
  -- Apply aux_m and naturality.
  have haux := integrateHeadBlock_flattenBasepointDiff_aux_m d n (d + 1) hm f u'
  have hLHS := hnat_m (d + 1) _ _ hab_eq hreix
    (flattenBasepointDiffSchwartz d n f) u'
  have hu'_symm : (castFinCLE hab_eq).symm u' = u := by
    ext i
    simp [u']
  rw [hu'_symm] at hLHS
  rw [← hLHS, haux]
  -- Simplify splitLast.
  have hsL : splitLast (d + 1 - (d + 1)) (n * (d + 1)) u' = u := by
    ext j
    show u' (Fin.natAdd (d + 1 - (d + 1)) j) = u j
    simp only [u', castFinCLE_apply_local]
    apply congrArg u
    apply Fin.ext
    simp [Fin.val_natAdd]
  simp_rw [hsL]
  -- Simplify basepointAssemble at m = d+1: it equals aHead ∘ Fin.rev.
  have hba : ∀ (aHead : Fin (d + 1) → ℝ),
      basepointAssemble d (d + 1) hm aHead
        (splitFirst (d + 1 - (d + 1)) (n * (d + 1)) u') =
      fun μ => aHead (Fin.rev μ) := by
    intro aHead
    ext μ
    show basepointAssemble d (d + 1) hm aHead
        (splitFirst (d + 1 - (d + 1)) (n * (d + 1)) u') μ = aHead (Fin.rev μ)
    simp only [basepointAssemble, castFinCLE_apply_local]
    set j := (finCongr (Nat.add_sub_of_le hm)).symm μ with hj_def
    have hj_val : j.val = μ.val := by simp [hj_def]
    have hj_lt : j.val < d + 1 := by
      have := μ.isLt; omega
    have hj_cast : j = Fin.castAdd (d + 1 - (d + 1)) ⟨j.val, hj_lt⟩ := by
      apply Fin.ext
      simp [Fin.val_castAdd]
    rw [hj_cast, Fin.addCases_left]
    apply congrArg aHead
    apply Fin.ext
    simp [hj_val]
  simp_rw [hba]
  -- Change of variable via (piCongrLeft Fin.revPerm).symm (aHead ↦ aHead ∘ Fin.rev).
  let ψ : (Fin (d + 1) → ℝ) ≃ᵐ (Fin (d + 1) → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm
  have hmp : MeasureTheory.MeasurePreserving ψ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (d + 1) → ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin (d + 1) → ℝ)) :=
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm _
  -- ψ aHead μ = aHead (Fin.rev μ) via piCongrLeft_symm_apply.
  have hψ_apply : ∀ (aHead : Fin (d + 1) → ℝ) (μ : Fin (d + 1)),
      ψ aHead μ = aHead (Fin.rev μ) := by
    intro aHead μ
    show (Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ) Fin.revPerm).symm aHead μ
      = aHead (Fin.rev μ)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  -- Change variable: ∫ aHead, integrand (ψ aHead) = ∫ a, integrand a
  rw [show
      (∫ aHead : Fin (d + 1) → ℝ,
        f (fun k μ =>
          aHead (Fin.rev μ) +
          diffVarSection d n ((flattenDiffCLE d n).symm u) k μ))
      =
      (∫ aHead : Fin (d + 1) → ℝ,
        (fun a : Fin (d + 1) → ℝ =>
          f (fun k μ =>
            a μ +
            diffVarSection d n ((flattenDiffCLE d n).symm u) k μ)) (ψ aHead))
      from by
        refine MeasureTheory.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro aHead
        simp only [hψ_apply]]
  exact hmp.integral_comp' (g := fun a : Fin (d + 1) → ℝ =>
    f (fun k μ =>
      a μ +
      diffVarSection d n ((flattenDiffCLE d n).symm u) k μ))

private lemma integrateHeadBlock_transport_eq_diffVarReduction
    (d : ℕ) [NeZero d] (n : ℕ)
    (f : SchwartzNPointSpace d (n + 1)) :
    integrateHeadBlock (m := d + 1) (n := n * (d + 1))
      (flattenBasepointDiffSchwartz d n f) =
    flattenSchwartzNPoint (d := d) (diffVarReduction d n f) := by
  ext u
  rw [flattenSchwartzNPoint_apply]
  change integrateHeadBlock (flattenBasepointDiffSchwartz d n f) u =
    ∫ a : Fin (d + 1) → ℝ,
      f (fun k μ => a μ + diffVarSection d n _ k μ)
  convert integrateHeadBlock_flattenBasepointDiff_aux d n f u using 1 <;> rfl

/-- The kernel theorem isolated in the blueprint: a diagonal-translation
invariant tempered distribution vanishes on the kernel of
`diffVarReduction`. The preferred proof route is the head-block transport
argument recorded in the blueprint. -/
private lemma translationInvariant_vanishesOn_diffVarReduction_kernel
    (d : ℕ) [NeZero d]
    (n : ℕ)
    {W : SchwartzNPointSpace d (n + 1) → ℂ}
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W)
    (hW_transl : ∀ (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d (n + 1)),
      (∀ x : NPointSpacetime d (n + 1),
        g.toFun x = f.toFun (fun i => x i + a)) →
      W f = W g) :
    ∀ f : SchwartzNPointSpace d (n + 1),
      diffVarReduction d n f = 0 → W f = 0 := by
  intro f hf
  let T := transportedWHeadBlockCLM d n W hW_cont hW_lin
  let F := flattenBasepointDiffSchwartz d n f
  have hT :
      IsHeadBlockTranslationInvariantSchwartzCLM
        (m := d + 1) (n := n * (d + 1)) T :=
    transportedWHeadBlockInvariant d n hW_cont hW_lin hW_transl
  have hIntF :
      integrateHeadBlock (m := d + 1) (n := n * (d + 1)) F = 0 := by
    simpa [F, hf] using integrateHeadBlock_transport_eq_diffVarReduction d n f
  have hmap :
      T F = T 0 := by
    exact map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant
      (m := d + 1) (n := n * (d + 1)) T hT F 0 (by
        have h0 : integrateHeadBlock (m := d + 1) (n := n * (d + 1)) 0 = 0 := by
          have h := integrateHeadBlock_sub (m := d + 1) (n := n * (d + 1)) F F
          simp [sub_self] at h; exact h
        rw [hIntF, h0])
  have hzeroT : T 0 = 0 := by
    have hW0 : W (0 : SchwartzNPointSpace d (n + 1)) = 0 := by
      simpa using (hW_lin.map_smul (0 : ℂ) (0 : SchwartzNPointSpace d (n + 1)))
    simpa [T, transportedWHeadBlockCLM, unflattenBasepointDiffSchwartz] using hW0
  calc
    W f = T F := by
      change W f = W (unflattenBasepointDiffSchwartz d n
        (flattenBasepointDiffSchwartz d n f))
      rw [unflatten_flattenBasepointDiffSchwartz]
    _ = T 0 := hmap
    _ = 0 := hzeroT

variable (d) in
/-- A fixed-arity diagonal-translation-invariant tempered distribution factors
through basepoint fiber reduction. -/
theorem exists_diffVar_distribution_fixed
    (n : ℕ)
    {W : SchwartzNPointSpace d (n + 1) → ℂ}
    (hW_cont : Continuous W)
    (hW_lin : IsLinearMap ℂ W)
    (hW_transl : ∀ (a : Fin (d + 1) → ℝ)
      (f g : SchwartzNPointSpace d (n + 1)),
      (∀ x : NPointSpacetime d (n + 1),
        g.toFun x = f.toFun (fun i => x i + a)) →
      W f = W g) :
    ∃ w : SchwartzNPointSpace d n →L[ℂ] ℂ,
      ∀ f : SchwartzNPointSpace d (n + 1),
        W f = w (diffVarReduction d n f) := by
  let φ₀ : SchwartzMap (BasepointSpace d) ℂ := normalizedBasepointBump d
  have hφ₀_int : ∫ a : BasepointSpace d, φ₀ a = 1 := by
    simpa [φ₀] using integral_normalizedBasepointBump d
  let φSect : SchwartzNPointSpace d n →L[ℂ] SchwartzNPointSpace d (n + 1) :=
    sectionOfCLM d n φ₀
  have hsection_right_inv :
      ∀ g : SchwartzNPointSpace d n, diffVarReduction d n (φSect g) = g := by
    intro g
    simpa [φSect, sectionOfCLM_apply] using
      diffVarReduction_sectionOf d n φ₀ hφ₀_int g
  let Wclm : SchwartzNPointSpace d (n + 1) →L[ℂ] ℂ :=
    { toFun := W
      map_add' := hW_lin.map_add
      map_smul' := hW_lin.map_smul
      cont := hW_cont }
  let w : SchwartzNPointSpace d n →L[ℂ] ℂ := Wclm.comp φSect
  refine ⟨w, fun f => ?_⟩
  have hred :
      diffVarReduction d n
          (f - φSect (diffVarReduction d n f)) = 0 := by
    rw [(diffVarReduction d n).map_sub, hsection_right_inv, sub_self]
  have hzero :
      W (f - φSect (diffVarReduction d n f)) = 0 :=
    translationInvariant_vanishesOn_diffVarReduction_kernel d n
      hW_cont hW_lin hW_transl _ hred
  change W f = W (φSect (diffVarReduction d n f))
  rw [← sub_eq_zero]
  simpa [hW_lin.map_sub] using hzero

/-- The constant-1 Schwartz function on the 0-dimensional spacetime. -/
private noncomputable def schwartzConstOne (d : ℕ) [NeZero d] : SchwartzNPointSpace d 0 :=
  ⟨fun _ => 1, contDiff_const, fun k n =>
    ⟨‖iteratedFDeriv ℝ n (fun _ : NPointSpacetime d 0 => (1 : ℂ)) 0‖, fun x => by
      rw [show x = 0 from Subsingleton.elim x 0, norm_zero]
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · rw [zero_pow hk, zero_mul]; exact norm_nonneg _⟩⟩

@[simp] private lemma schwartzConstOne_apply (d : ℕ) [NeZero d] (x : NPointSpacetime d 0) :
    schwartzConstOne d x = 1 := rfl
