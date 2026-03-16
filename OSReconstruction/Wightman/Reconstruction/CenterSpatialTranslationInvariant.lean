import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.DenseCLM

open scoped SchwartzMap

noncomputable section

namespace OSReconstruction

/-- Reindex ordinary Euclidean Schwartz space along an equivalence of `Fin`
index sets. -/
def reindexSchwartzEquiv {a b : ℕ} (σ : Fin a ≃ Fin b) :
    SchwartzMap (Fin a → ℝ) ℂ →L[ℂ] SchwartzMap (Fin b → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.funCongrLeft ℝ ℝ σ).toContinuousLinearEquiv)

@[simp] theorem reindexSchwartzEquiv_apply {a b : ℕ} (σ : Fin a ≃ Fin b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) (x : Fin b → ℝ) :
    reindexSchwartzEquiv σ F x = F ((LinearEquiv.funCongrLeft ℝ ℝ σ) x) := by
  rfl

private def centerSpatialFirstPermAux (d : ℕ) :
    Fin d ⊕ Fin (d + 2) ≃ Fin (d + 1) ⊕ Fin (d + 1) :=
  { toFun := fun s =>
      match s with
      | Sum.inl i => Sum.inl i.succ
      | Sum.inr j => Fin.cases (motive := fun _ => Fin (d + 1) ⊕ Fin (d + 1))
          (Sum.inl 0) (fun k => Sum.inr k) j
    invFun := fun s =>
      match s with
      | Sum.inl i => Fin.cases (motive := fun _ => Fin d ⊕ Fin (d + 2))
          (Sum.inr 0) (fun k => Sum.inl k) i
      | Sum.inr j => Sum.inr (Fin.succ j)
    left_inv := by
      intro s
      rcases s with i | j
      · simp
      · refine Fin.cases ?_ ?_ j
        · rfl
        · intro k
          rfl
    right_inv := by
      intro s
      rcases s with i | j
      · refine Fin.cases ?_ ?_ i
        · rfl
        · intro k
          rfl
      · rfl }

/-- Reorder flattened two-point center/difference coordinates so that the `d`
center-spatial coordinates come first, followed by the center-time coordinate
and the full difference block. -/
def centerSpatialFirstPerm (d : ℕ) :
    Fin (d + (d + 2)) ≃ Fin ((d + 1) + (d + 1)) :=
  (finSumFinEquiv.symm.trans (centerSpatialFirstPermAux d)).trans finSumFinEquiv

@[simp] theorem centerSpatialFirstPerm_symm_castAdd_zero (d : ℕ) :
    (centerSpatialFirstPerm d).symm (Fin.castAdd (d + 1) (0 : Fin (d + 1))) =
      Fin.natAdd d (0 : Fin (d + 2)) := by
  apply Fin.ext
  simp [centerSpatialFirstPerm, centerSpatialFirstPermAux]

@[simp] theorem centerSpatialFirstPerm_symm_castAdd_succ (d : ℕ) (i : Fin d) :
    (centerSpatialFirstPerm d).symm (Fin.castAdd (d + 1) i.succ) =
      Fin.castAdd (d + 2) i := by
  apply Fin.ext
  simp [centerSpatialFirstPerm, centerSpatialFirstPermAux]

@[simp] theorem centerSpatialFirstPerm_symm_natAdd (d : ℕ) (i : Fin (d + 1)) :
    (centerSpatialFirstPerm d).symm (Fin.natAdd (d + 1) i) =
      Fin.natAdd d i.succ := by
  change finSumFinEquiv
      ((centerSpatialFirstPermAux d).symm
        (finSumFinEquiv.symm (Fin.natAdd (d + 1) i))) =
    Fin.natAdd d i.succ
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp [centerSpatialFirstPermAux]

/-- Translation of only the center-spatial coordinates in flattened two-point
center/difference variables. -/
def centerSpatialShift (d : ℕ) (a : Fin d → ℝ) :
    Fin ((d + 1) + (d + 1)) → ℝ :=
  fun i =>
    zeroTailBlockShift (m := d) (n := d + 2) a ((centerSpatialFirstPerm d).symm i)

private theorem reindexSchwartzEquiv_translate {a b : ℕ} (σ : Fin a ≃ Fin b)
    (v : Fin a → ℝ) (F : SchwartzMap (Fin a → ℝ) ℂ) :
    reindexSchwartzEquiv σ (SCV.translateSchwartz v F) =
      SCV.translateSchwartz
        (((LinearEquiv.funCongrLeft ℝ ℝ σ).symm) v)
        (reindexSchwartzEquiv σ F) := by
  ext x
  simp [reindexSchwartzEquiv, SCV.translateSchwartz_apply]
  congr 1
  ext i
  simp

private theorem centerSpatialShift_pullback_symm
    (d : ℕ) (a : Fin d → ℝ) :
    ((LinearEquiv.funCongrLeft ℝ ℝ (centerSpatialFirstPerm d).symm).symm)
        (centerSpatialShift d a) =
      zeroTailBlockShift (m := d) (n := d + 2) a := by
  ext i
  simp [centerSpatialShift]

private theorem centerSpatialShift_pushforward
    (d : ℕ) (a : Fin d → ℝ) :
    ((LinearEquiv.funCongrLeft ℝ ℝ (centerSpatialFirstPerm d)).symm)
        (zeroTailBlockShift (m := d) (n := d + 2) a) =
      centerSpatialShift d a := by
  ext i
  simp [centerSpatialShift]

private theorem reindexSchwartzEquiv_left_right_inv {a b : ℕ} (σ : Fin a ≃ Fin b)
    (F : SchwartzMap (Fin b → ℝ) ℂ) :
    reindexSchwartzEquiv σ (reindexSchwartzEquiv σ.symm F) = F := by
  ext x
  have hx :
      ((LinearEquiv.funCongrLeft ℝ ℝ σ.symm)
        (((LinearEquiv.funCongrLeft ℝ ℝ σ) x))) = x := by
    ext i
    simp
  simpa [reindexSchwartzEquiv] using congrArg F hx

/-- A scalar Schwartz functional on flattened two-point center/difference
coordinates is center-spatial translation invariant if translating only the
`d` center-spatial coordinates leaves it unchanged. -/
def IsCenterSpatialTranslationInvariantSchwartzCLM
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ a : Fin d → ℝ,
    T.comp (SCV.translateSchwartzCLM (centerSpatialShift d a)) = T

theorem centerSpatialInvariant_to_headBlockInvariant
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T) :
    IsHeadBlockTranslationInvariantSchwartzCLM (m := d) (n := d + 2)
      (T.comp (reindexSchwartzEquiv (centerSpatialFirstPerm d))) := by
  intro a
  ext F
  change
    T (reindexSchwartzEquiv (centerSpatialFirstPerm d)
      (SCV.translateSchwartz (zeroTailBlockShift (m := d) (n := d + 2) a) F)) =
      T (reindexSchwartzEquiv (centerSpatialFirstPerm d) F)
  rw [reindexSchwartzEquiv_translate]
  rw [centerSpatialShift_pushforward]
  have := congrArg
    (fun S : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
      S (reindexSchwartzEquiv (centerSpatialFirstPerm d) F))
    (hT a)
  simpa [ContinuousLinearMap.comp_apply, SCV.translateSchwartzCLM_apply] using this

/-- Integrate out only the center-spatial coordinates in flattened two-point
center/difference variables, leaving the center-time coordinate and the full
difference block untouched. -/
def integrateCenterSpatial (d : ℕ)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ) :
    SchwartzMap (Fin (d + 2) → ℝ) ℂ :=
  integrateHeadBlock (m := d) (n := d + 2)
    (reindexSchwartzEquiv (centerSpatialFirstPerm d).symm F)

/-- Integrating out the center-spatial block is invariant under translating
exactly those center-spatial coordinates. -/
theorem integrateCenterSpatial_translate_centerSpatial
    (d : ℕ) (a : Fin d → ℝ)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ) :
    integrateCenterSpatial d (SCV.translateSchwartz (centerSpatialShift d a) F) =
      integrateCenterSpatial d F := by
  rw [integrateCenterSpatial, reindexSchwartzEquiv_translate]
  rw [centerSpatialShift_pullback_symm]
  simpa using
    integrateHeadBlock_translateSchwartz_head
      (m := d) (n := d + 2) a
      (reindexSchwartzEquiv (centerSpatialFirstPerm d).symm F)

/-- A center-spatial-translation-invariant functional depends only on the test
after integrating out the center-spatial coordinates. -/
theorem map_eq_of_integrateCenterSpatial_eq_of_centerSpatialInvariant
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (F G : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ)
    (hFG : integrateCenterSpatial d F = integrateCenterSpatial d G) :
    T F = T G := by
  let T' :
      SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp (reindexSchwartzEquiv (centerSpatialFirstPerm d))
  let F' : SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ :=
    reindexSchwartzEquiv (centerSpatialFirstPerm d).symm F
  let G' : SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ :=
    reindexSchwartzEquiv (centerSpatialFirstPerm d).symm G
  have hT' :
      IsHeadBlockTranslationInvariantSchwartzCLM (m := d) (n := d + 2) T' :=
    centerSpatialInvariant_to_headBlockInvariant d T hT
  have hFG' : integrateHeadBlock (m := d) (n := d + 2) F' =
      integrateHeadBlock (m := d) (n := d + 2) G' := by
    simpa [integrateCenterSpatial, F', G'] using hFG
  have hmain :=
    map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant
      (m := d) (n := d + 2) T' hT' F' G' hFG'
  have hFinv :
      reindexSchwartzEquiv (centerSpatialFirstPerm d) F' = F :=
    reindexSchwartzEquiv_left_right_inv (centerSpatialFirstPerm d) F
  have hGinv :
      reindexSchwartzEquiv (centerSpatialFirstPerm d) G' = G :=
    reindexSchwartzEquiv_left_right_inv (centerSpatialFirstPerm d) G
  have hFid : T F = T' F' := by
    change T F = T ((reindexSchwartzEquiv (centerSpatialFirstPerm d)) F')
    rw [hFinv]
  have hGid : T G = T' G' := by
    change T G = T ((reindexSchwartzEquiv (centerSpatialFirstPerm d)) G')
    rw [hGinv]
  simpa [hFid, hGid] using hmain

/-- If a normalized center-spatial cutoff `φ` is fixed, then a
center-spatial-translation-invariant functional factors through
`integrateCenterSpatial` by tensoring `φ` back in. -/
theorem map_eq_tensorProduct_integrateCenterSpatial_of_centerSpatialInvariant
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ) :
    T F =
      T (reindexSchwartzEquiv (centerSpatialFirstPerm d)
        (φ.tensorProduct
          (integrateCenterSpatial d F))) := by
  let T' :
      SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp (reindexSchwartzEquiv (centerSpatialFirstPerm d))
  let F' : SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ :=
    reindexSchwartzEquiv (centerSpatialFirstPerm d).symm F
  have hT' :
      IsHeadBlockTranslationInvariantSchwartzCLM (m := d) (n := d + 2) T' :=
    centerSpatialInvariant_to_headBlockInvariant d T hT
  have hmain :=
    map_eq_tensorProduct_integrateHeadBlock_of_headBlockTranslationInvariant
      (m := d) (n := d + 2) T' hT' φ hφ F'
  have hFid : reindexSchwartzEquiv (centerSpatialFirstPerm d) F' = F :=
    reindexSchwartzEquiv_left_right_inv (centerSpatialFirstPerm d) F
  calc
    T F = T' F' := by
      simpa [T', F', hFid]
    _ = T' (φ.tensorProduct (integrateHeadBlock (m := d) (n := d + 2) F')) := hmain
    _ = T (reindexSchwartzEquiv (centerSpatialFirstPerm d)
          (φ.tensorProduct
            (integrateCenterSpatial d F))) := by
          change T ((reindexSchwartzEquiv (centerSpatialFirstPerm d))
            (φ.tensorProduct (integrateHeadBlock (m := d) (n := d + 2) F')))
            =
            T ((reindexSchwartzEquiv (centerSpatialFirstPerm d))
              (φ.tensorProduct (integrateCenterSpatial d F)))
          simp [integrateCenterSpatial, F']

/-- Reinsert a reduced center-time/difference test into the full flattened
two-point center/difference space by tensoring with a fixed center-spatial
cutoff and undoing the center-spatial permutation. -/
noncomputable def centerSpatialSectionCLM
    (d : ℕ) (φ : SchwartzMap (Fin d → ℝ) ℂ) :
    SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ :=
  let tensorRight :
      SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin (d + (d + 2)) → ℝ) ℂ :=
    { toLinearMap :=
        { toFun := fun H => φ.tensorProduct H
          map_add' := by
            intro H K
            ext x
            simp [SchwartzMap.tensorProduct_apply, mul_add]
          map_smul' := by
            intro c H
            ext x
            simp [SchwartzMap.tensorProduct_apply, mul_comm, mul_left_comm, mul_assoc] }
      cont := SchwartzMap.tensorProduct_continuous_right φ }
  (reindexSchwartzEquiv (centerSpatialFirstPerm d)).comp tensorRight

/-- Descend a center-spatial-translation-invariant functional to the reduced
center-time/difference Schwartz space by fixing a normalized center-spatial
cutoff. -/
noncomputable def centerSpatialDescentCLM
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin d → ℝ) ℂ) :
    SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ] ℂ :=
  T.comp (centerSpatialSectionCLM d φ)

/-- Reinserted reduced tests survive center-spatial integration unchanged when
the fixed center-spatial cutoff integrates to `1`. -/
@[simp] theorem integrateCenterSpatial_centerSpatialSectionCLM
    (d : ℕ) (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (H : SchwartzMap (Fin (d + 2) → ℝ) ℂ) :
    integrateCenterSpatial d (centerSpatialSectionCLM d φ H) = H := by
  have hreindex :
      reindexSchwartzEquiv (centerSpatialFirstPerm d).symm
        (reindexSchwartzEquiv (centerSpatialFirstPerm d) (φ.tensorProduct H)) =
      φ.tensorProduct H := by
    simpa using
      reindexSchwartzEquiv_left_right_inv (centerSpatialFirstPerm d).symm
        (φ.tensorProduct H)
  rw [centerSpatialSectionCLM, ContinuousLinearMap.comp_apply, integrateCenterSpatial]
  dsimp
  rw [hreindex, integrateHeadBlock_tensorProduct, SchwartzMap.integralCLM_apply, hφ, one_smul]

/-- Any functional that factors through `integrateCenterSpatial` is
automatically invariant under center-spatial translations. -/
theorem isCenterSpatialTranslationInvariant_of_factors_through_integrateCenterSpatial
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (R : SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ] ℂ)
    (hfac : ∀ F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ,
      T F = R (integrateCenterSpatial d F)) :
    IsCenterSpatialTranslationInvariantSchwartzCLM d T := by
  intro a
  ext F
  rw [ContinuousLinearMap.comp_apply, hfac, hfac, SCV.translateSchwartzCLM_apply,
    integrateCenterSpatial_translate_centerSpatial]

/-- If a functional factors through `integrateCenterSpatial`, then its
center-spatial descent recovers exactly that reduced functional. -/
theorem centerSpatialDescentCLM_eq_of_factors_through_integrateCenterSpatial
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (R : SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (hfac : ∀ F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ,
      T F = R (integrateCenterSpatial d F)) :
    centerSpatialDescentCLM d T φ = R := by
  ext H
  rw [centerSpatialDescentCLM, ContinuousLinearMap.comp_apply, hfac]
  simp [integrateCenterSpatial_centerSpatialSectionCLM, hφ]

/-- If the center-spatial cutoff `φ` is normalized by `∫ φ = 1`, then a
center-spatial-translation-invariant functional factors through
`integrateCenterSpatial` via `centerSpatialDescentCLM T φ`. -/
theorem map_eq_centerSpatialDescentCLM_integrateCenterSpatial_of_centerSpatialInvariant
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ) :
    T F = centerSpatialDescentCLM d T φ (integrateCenterSpatial d F) := by
  simpa [centerSpatialDescentCLM, centerSpatialSectionCLM] using
    map_eq_tensorProduct_integrateCenterSpatial_of_centerSpatialInvariant
      d T hT φ hφ F

/-- If a full flattened two-point functional is center-spatial translation
invariant and its descended `(u_time, ξ)` functional is head-translation
invariant, then the original functional depends only on the iterated reduced
descent `sliceIntegral ∘ integrateCenterSpatial`. This is the OS-II-shaped
"integrate spatial parameters first, then the active time variable" reduction
surface. -/
theorem map_eq_headTranslationDescentCLM_sliceIntegral_integrateCenterSpatial
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ t : ℝ, ψ t = 1)
    (hTred : IsHeadTranslationInvariantSchwartzCLM (centerSpatialDescentCLM d T φ))
    (F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ) :
    T F =
      headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ
        (sliceIntegral (integrateCenterSpatial d F)) := by
  calc
    T F = centerSpatialDescentCLM d T φ (integrateCenterSpatial d F) := by
      exact map_eq_centerSpatialDescentCLM_integrateCenterSpatial_of_centerSpatialInvariant
        d T hT φ hφ F
    _ = headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ
          (sliceIntegral (integrateCenterSpatial d F)) := by
        simpa [headTranslationDescentCLM] using
          map_eq_headTranslationDescentCLM_sliceIntegral_of_headTranslationInvariant
            (centerSpatialDescentCLM d T φ) hTred ψ hψ (integrateCenterSpatial d F)

/-- If a full-space functional factors through `integrateCenterSpatial`, and
the reduced functional then factors through `sliceIntegral`, the final descended
functional is exactly the quotient functional on the `(u_time, ξ)` surface. -/
theorem headTranslationDescentCLM_centerSpatialDescentCLM_eq_of_twoStageFactorization
    (d : ℕ)
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (R : SchwartzMap (Fin (d + 2) → ℝ) ℂ →L[ℂ] ℂ)
    (L : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ t : ℝ, ψ t = 1)
    (hTfac : ∀ F : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ,
      T F = R (integrateCenterSpatial d F))
    (hRfac : ∀ H : SchwartzMap (Fin (d + 2) → ℝ) ℂ, R H = L (sliceIntegral H)) :
    headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ = L := by
  have hdesc :
      centerSpatialDescentCLM d T φ = R :=
    centerSpatialDescentCLM_eq_of_factors_through_integrateCenterSpatial
      d T R φ hφ hTfac
  rw [hdesc]
  exact
    headTranslationDescentCLM_eq_of_factors_through_sliceIntegral
      R L ψ hψ hRfac

/-- To identify two full flattened two-point functionals, it is enough to
identify their reduced `(u_time, ξ)` descended functionals on a dense subset.
This is the clean quotient-level equality principle behind the OS-II-style
"integrate center-spatial variables first, then the active time variable"
route. -/
theorem eq_of_eq_on_dense_headTranslationDescentCLM_centerSpatial
    (d : ℕ)
    (T U : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hT : IsCenterSpatialTranslationInvariantSchwartzCLM d T)
    (hU : IsCenterSpatialTranslationInvariantSchwartzCLM d U)
    (φ : SchwartzMap (Fin d → ℝ) ℂ)
    (hφ : ∫ x : Fin d → ℝ, φ x = 1)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ : ∫ t : ℝ, ψ t = 1)
    (hTred : IsHeadTranslationInvariantSchwartzCLM (centerSpatialDescentCLM d T φ))
    (hUred : IsHeadTranslationInvariantSchwartzCLM (centerSpatialDescentCLM d U φ))
    {S : Set (SchwartzMap (Fin (d + 1) → ℝ) ℂ)}
    (hS : Dense S)
    (hEq : ∀ f ∈ S,
      headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ f =
        headTranslationDescentCLM (centerSpatialDescentCLM d U φ) ψ f) :
    T = U := by
  have hdescEq :
      headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ =
        headTranslationDescentCLM (centerSpatialDescentCLM d U φ) ψ :=
    ContinuousLinearMap.eq_of_eq_on_dense
      (headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ)
      (headTranslationDescentCLM (centerSpatialDescentCLM d U φ) ψ)
      hS (by
        intro f hf
        exact hEq f hf)
  ext F
  calc
    T F =
        headTranslationDescentCLM (centerSpatialDescentCLM d T φ) ψ
          (sliceIntegral (integrateCenterSpatial d F)) := by
            exact
              map_eq_headTranslationDescentCLM_sliceIntegral_integrateCenterSpatial
                d T hT φ hφ ψ hψ hTred F
    _ =
        headTranslationDescentCLM (centerSpatialDescentCLM d U φ) ψ
          (sliceIntegral (integrateCenterSpatial d F)) := by
            simpa using congrArg
              (fun R : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ =>
                R (sliceIntegral (integrateCenterSpatial d F))) hdescEq
    _ = U F := by
            symm
            exact
              map_eq_headTranslationDescentCLM_sliceIntegral_integrateCenterSpatial
                d U hU φ hφ ψ hψ hUred F

end OSReconstruction
