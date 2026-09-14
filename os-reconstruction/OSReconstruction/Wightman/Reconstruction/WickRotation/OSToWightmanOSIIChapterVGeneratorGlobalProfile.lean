/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorFullSourceProvenance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTimeSpatialTensor
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.SchwartzTensorProduct














noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace GeneratorHermiteHilbertFieldFamilyData

variable {d k : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

private theorem blockwiseSpacetimeDiff_symm_time
    {n m : ℕ}
    (q : NPointDomain d (n + m)) :
    (fun c =>
      (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q c 0) =
      (osiiAxisPairBlockwiseTimeDiffCLE n m).symm
        (fun c => q c 0) := by
  funext c
  refine Fin.addCases ?_ ?_ c
  · intro a
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    simp [section43ScalarDiffCLE_symm_apply, splitFirst]
  · intro b
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
    simp [section43ScalarDiffCLE_symm_apply, splitLast]

private theorem reflectReverseLeftSpacetime_time
    {n m : ℕ}
    (x : NPointDomain d (n + m)) :
    (fun c =>
      osiiAxisPairReflectReverseLeftSpacetimeCLE d n m x c 0) =
      osiiAxisPairReflectReverseLeftTimeCLE n m
        (fun c => x c 0) := by
  funext c
  refine Fin.addCases ?_ ?_ c
  · intro a
    simp [timeReflection]
  · intro b
    simp

private theorem section43DiffCoordRealCLE_time
    {n : ℕ}
    (x : NPointDomain d n) :
    (fun c => section43DiffCoordRealCLE d n x c 0) =
      section43ScalarDiffCLE n (fun c => x c 0) := by
  funext c
  simp [section43ScalarDiffCLE_apply]

private theorem blockGlobalSpacetime_time
    {n m : ℕ}
    (q : NPointDomain d (n + m)) :
    (fun c => osiiAxisPairBlockGlobalSpacetimeCLE d n m q c 0) =
      osiiAxisPairBlockGlobalTimeCLE n m (fun c => q c 0) := by
  change
    (fun c =>
      section43DiffCoordRealCLE d (n + m)
        (osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)) c 0) =
      section43ScalarDiffCLE (n + m)
        (osiiAxisPairReflectReverseLeftTimeCLE n m
          ((osiiAxisPairBlockwiseTimeDiffCLE n m).symm
            (fun c => q c 0)))
  rw [section43DiffCoordRealCLE_time]
  congr 1
  rw [reflectReverseLeftSpacetime_time,
    blockwiseSpacetimeDiff_symm_time]

private theorem blockGlobalSpacetime_time_eq_zero
    {n m : ℕ}
    (η : Section43SpatialSpace d (n + m)) :
    (fun c =>
      osiiAxisPairBlockGlobalSpacetimeCLE d n m
        ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η)) c 0) = 0 := by
  have hinput :
      (fun c =>
        (nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η) c 0) = 0 := by
    exact congrArg Prod.fst
      ((nPointTimeSpatialCLE (d := d) (n + m)).apply_symm_apply (0, η))
  rw [blockGlobalSpacetime_time]
  rw [hinput, map_zero]

private theorem blockGlobalSpacetime_symm_time_eq_zero
    {n m : ℕ}
    (η : Section43SpatialSpace d (n + m)) :
    (fun c =>
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
        ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η)) c 0) = 0 := by
  let q :=
    (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
      ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η))
  have hmap :
      osiiAxisPairBlockGlobalTimeCLE n m (fun c => q c 0) = 0 := by
    rw [← blockGlobalSpacetime_time]
    change
      (fun c =>
        osiiAxisPairBlockGlobalSpacetimeCLE d n m q c 0) = 0
    rw [(osiiAxisPairBlockGlobalSpacetimeCLE d n m).apply_symm_apply]
    exact congrArg Prod.fst
      ((nPointTimeSpatialCLE (d := d) (n + m)).apply_symm_apply (0, η))
  have hzero :
      (fun c => q c 0) = 0 :=
    (osiiAxisPairBlockGlobalTimeCLE n m).injective (by
      simpa using hmap)
  exact hzero

/-- The spatial block of the block-global spacetime chart. The common and
right-block shifts are purely temporal, so this is the complete spatial
dependence of the affine chart. -/
noncomputable def axisPairBlockGlobalSpatialCLE
    (n m : ℕ) :
    Section43SpatialSpace d (n + m) ≃L[ℝ]
      Section43SpatialSpace d (n + m) where
  toFun := fun η =>
    section43QSpatial (d := d) (n := n + m)
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m
        ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η)))
  invFun := fun η =>
    section43QSpatial (d := d) (n := n + m)
      ((osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
        ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η)))
  map_add' := by
    intro η ζ
    change
      ((nPointTimeSpatialCLE (d := d) (n + m))
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, η + ζ)))).2 = _
    have hsymm :
        (nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, η + ζ) =
          (nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η) +
            (nPointTimeSpatialCLE (d := d) (n + m)).symm (0, ζ) := by
      rw [show
        ((0 : Fin (n + m) → ℝ), η + ζ) =
          ((0 : Fin (n + m) → ℝ), η) +
            ((0 : Fin (n + m) → ℝ), ζ) by ext <;> simp]
      exact map_add _ _ _
    rw [hsymm, map_add, map_add]
    rfl
  map_smul' := by
    intro r η
    change
      ((nPointTimeSpatialCLE (d := d) (n + m))
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, r • η)))).2 = _
    have hsymm :
        (nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, r • η) =
          r • (nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, η) := by
      rw [show
        ((0 : Fin (n + m) → ℝ), r • η) =
          r • ((0 : Fin (n + m) → ℝ), η) by ext <;> simp]
      exact map_smul _ _ _
    rw [hsymm, map_smul, map_smul]
    rfl
  left_inv := by
    intro η
    let q := (nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η)
    let y := osiiAxisPairBlockGlobalSpacetimeCLE d n m q
    have hy :
        (nPointTimeSpatialCLE (d := d) (n + m)) y =
          (0, section43QSpatial (d := d) (n := n + m) y) := by
      apply Prod.ext
      · exact blockGlobalSpacetime_time_eq_zero η
      · rfl
    change
      section43QSpatial (d := d) (n := n + m)
        ((osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, section43QSpatial (d := d) (n := n + m) y))) = η
    rw [← hy, (nPointTimeSpatialCLE (d := d) (n + m)).symm_apply_apply,
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm_apply_apply]
    rfl
  right_inv := by
    intro η
    let q :=
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
        ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η))
    have hq :
        (nPointTimeSpatialCLE (d := d) (n + m)) q =
          (0, section43QSpatial (d := d) (n := n + m) q) := by
      apply Prod.ext
      · exact blockGlobalSpacetime_symm_time_eq_zero η
      · rfl
    change
      section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, section43QSpatial (d := d) (n := n + m) q))) = η
    rw [← hq, (nPointTimeSpatialCLE (d := d) (n + m)).symm_apply_apply,
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m).apply_symm_apply]
    rfl
  continuous_toFun := by
    change Continuous (fun η =>
      ((nPointTimeSpatialCLE (d := d) (n + m))
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, η)))).2)
    exact continuous_snd.comp <|
      (nPointTimeSpatialCLE (d := d) (n + m)).continuous.comp <|
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m).continuous.comp <|
          (nPointTimeSpatialCLE (d := d) (n + m)).symm.continuous.comp <|
            continuous_const.prodMk continuous_id
  continuous_invFun := by
    change Continuous (fun η =>
      ((nPointTimeSpatialCLE (d := d) (n + m))
        ((osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm
            (0, η)))).2)
    exact continuous_snd.comp <|
      (nPointTimeSpatialCLE (d := d) (n + m)).continuous.comp <|
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm.continuous.comp <|
          (nPointTimeSpatialCLE (d := d) (n + m)).symm.continuous.comp <|
            continuous_const.prodMk continuous_id

@[simp] theorem axisPairBlockGlobalSpatialCLE_apply
    (n m : ℕ)
    (η : Section43SpatialSpace d (n + m)) :
    axisPairBlockGlobalSpatialCLE (d := d) n m η =
      section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m
          ((nPointTimeSpatialCLE (d := d) (n + m)).symm (0, η))) := rfl

private theorem blockGlobalSpacetime_spatial_eq_zero
    {n m : ℕ}
    (q : NPointDomain d (n + m))
    (hq : ∀ c (j : Fin d), q c j.succ = 0)
    (c : Fin (n + m))
    (j : Fin d) :
    osiiAxisPairBlockGlobalSpacetimeCLE d n m q c j.succ = 0 := by
  have habs :
      ∀ c,
        (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q c j.succ = 0 := by
    intro c
    refine Fin.addCases ?_ ?_ c
    · intro a
      rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left,
        section43DiffCoordRealCLE_symm_apply]
      apply Finset.sum_eq_zero
      intro r hr
      exact hq _ j
    · intro b
      rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right,
        section43DiffCoordRealCLE_symm_apply]
      apply Finset.sum_eq_zero
      intro r hr
      exact hq _ j
  have hreflect :
      ∀ c,
        osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)
          c j.succ = 0 := by
    intro c
    refine Fin.addCases ?_ ?_ c
    · intro a
      rw [osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_left]
      simp [timeReflection, habs]
    · intro b
      rw [osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_right]
      exact habs _
  change
    section43DiffCoordRealCLE d (n + m)
      (osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
        ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q))
      c j.succ = 0
  rw [section43DiffCoordRealCLE_apply]
  split_ifs <;> simp [hreflect]

private theorem blockGlobalSpacetime_spatial
    {n m : ℕ}
    (q : NPointDomain d (n + m)) :
    section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m q) =
      axisPairBlockGlobalSpatialCLE (d := d) n m
        (section43QSpatial (d := d) (n := n + m) q) := by
  let e := nPointTimeSpatialCLE (d := d) (n + m)
  let qtime : NPointDomain d (n + m) :=
    e.symm (section43QTime (d := d) (n := n + m) q, 0)
  let qspatial : NPointDomain d (n + m) :=
    e.symm (0, section43QSpatial (d := d) (n := n + m) q)
  have hq : q = qtime + qspatial := by
    apply e.injective
    rw [map_add, e.apply_symm_apply, e.apply_symm_apply]
    change
      e q =
        (section43QTime (d := d) (n := n + m) q, 0) +
          (0, section43QSpatial (d := d) (n := n + m) q)
    simp [section43QTime, section43QSpatial, e]
  have htime_spatial :
      section43QSpatial (d := d) (n := n + m)
          (osiiAxisPairBlockGlobalSpacetimeCLE d n m qtime) = 0 := by
    apply (EuclideanSpace.equiv
      (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).injective
    funext p
    rw [section43QSpatial_apply]
    apply blockGlobalSpacetime_spatial_eq_zero
    intro c j
    dsimp [qtime, e]
    have h :=
      congrArg Prod.snd
        ((nPointTimeSpatialCLE (d := d) (n + m)).apply_symm_apply
          (section43QTime (d := d) (n := n + m) q, 0))
    have hzero :
        section43QSpatial (d := d) (n := n + m) qtime = 0 := h
    have hc :=
      congrArg
        (fun η =>
          (EuclideanSpace.equiv
            (ι := Fin (n + m) × Fin d) (𝕜 := ℝ) η) (c, j))
        hzero
    simpa [section43QSpatial_apply] using hc
  calc
    section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m q) =
      section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m qtime +
          osiiAxisPairBlockGlobalSpacetimeCLE d n m qspatial) := by
            rw [hq, map_add]
    _ =
      section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m qspatial) := by
          change
            (e
              (osiiAxisPairBlockGlobalSpacetimeCLE d n m qtime +
                osiiAxisPairBlockGlobalSpacetimeCLE d n m qspatial)).2 =
              (e
                (osiiAxisPairBlockGlobalSpacetimeCLE d n m qspatial)).2
          rw [map_add, Prod.snd_add]
          have htime_spatial' :
              (e
                (osiiAxisPairBlockGlobalSpacetimeCLE d n m qtime)).2 = 0 :=
            htime_spatial
          rw [htime_spatial', zero_add]
    _ =
      axisPairBlockGlobalSpatialCLE (d := d) n m
        (section43QSpatial (d := d) (n := n + m) q) := by
          rfl

private theorem globalSpacetimeDiffShift_spatial_eq_zero
    (n m : ℕ) (s t : ℝ) :
    section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairGlobalSpacetimeDiffShift d n m s t) = 0 := by
  apply (EuclideanSpace.equiv
    (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)).injective
  funext p
  rw [section43QSpatial_apply]
  simp [osiiAxisPairGlobalSpacetimeDiffShift,
    osiiAxisPairGlobalAbsoluteSpacetimeShift,
    section43DiffCoordRealCLE_apply, timeShiftVec]

private theorem blockGlobalSpacetimeAffine_spatial
    {n m : ℕ}
    (s t : ℝ)
    (q : NPointDomain d (n + m)) :
    section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q) =
      axisPairBlockGlobalSpatialCLE (d := d) n m
        (section43QSpatial (d := d) (n := n + m) q) := by
  rw [osiiAxisPairBlockGlobalSpacetimeAffine]
  calc
    section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m q +
          osiiAxisPairGlobalSpacetimeDiffShift d n m s t) =
      section43QSpatial (d := d) (n := n + m)
          (osiiAxisPairBlockGlobalSpacetimeCLE d n m q) +
        section43QSpatial (d := d) (n := n + m)
          (osiiAxisPairGlobalSpacetimeDiffShift d n m s t) := by
            change
              ((nPointTimeSpatialCLE (d := d) (n + m))
                (osiiAxisPairBlockGlobalSpacetimeCLE d n m q +
                  osiiAxisPairGlobalSpacetimeDiffShift d n m s t)).2 = _
            rw [map_add, Prod.snd_add]
            rfl
    _ =
      section43QSpatial (d := d) (n := n + m)
        (osiiAxisPairBlockGlobalSpacetimeCLE d n m q) := by
          rw [globalSpacetimeDiffShift_spatial_eq_zero, add_zero]
    _ =
      axisPairBlockGlobalSpatialCLE (d := d) n m
        (section43QSpatial (d := d) (n := n + m) q) :=
          blockGlobalSpacetime_spatial q

/-- Pull a split spatial test from the separate block chart to the global
difference-coordinate chart. -/
noncomputable def axisPairGlobalSpatialPullbackCLM
    (n m : ℕ) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (n + m)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (axisPairBlockGlobalSpatialCLE (d := d) n m).symm

/-- Corrected block-global normal form. Both the time cutoff and the spatial
test are transported by the affine chart; only the former sees the affine
translation. -/
theorem axisPairGlobalAbsoluteSpatialSourceCLM_normalForm
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ) :
    axisPairGlobalAbsoluteSpatialSourceCLM
        (d := d) n m η₁ η₂ s t =
      (section43OrderedPullbackTimeSpatialTensorSpatialCLM
        d (n + m)
        (osiiAxisPairGlobalTimeCutoff n m η₁.conj η₂ s t)).comp
          (axisPairGlobalSpatialPullbackCLM
            (d := d) n m) := by
  ext F x
  obtain ⟨q, hq⟩ :=
    osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_surjective
      (d := d) n m t (fun c => x c + (-timeShiftVec d s))
  have hshift :
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q = x := by
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_commonShift, hq]
    ext c μ
    simp [timeShiftVec]
  rw [← hshift,
    axisPairGlobalAbsoluteSpatialSourceCLM_config]
  change
    η₁.conj (fun a => q (Fin.castAdd m a) 0) *
          η₂ (fun b => q (Fin.natAdd n b) 0) *
          F (section43QSpatial (d := d) (n := n + m) q) =
      section43NPointTimeSpatialTensor d (n + m)
        (osiiAxisPairGlobalTimeCutoff n m η₁.conj η₂ s t)
        (axisPairGlobalSpatialPullbackCLM (d := d) n m F)
        (section43DiffCoordRealCLE d (n + m)
          (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
            d n m s t q))
  rw [section43DiffCoordRealCLE_blockGlobalAbsoluteSpacetimeConfig,
    section43NPointTimeSpatialTensor_apply]
  have htime :
      section43QTime (d := d) (n := n + m)
          (osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q) =
        osiiAxisPairBlockGlobalTimeAffine n m s t
          (fun c => q c 0) :=
    osiiAxisPairBlockGlobalSpacetimeAffine_time
      d n m hn hm s t q
  rw [htime, osiiAxisPairGlobalTimeCutoff_affine,
    blockGlobalSpacetimeAffine_spatial]
  change
    η₁.conj (fun a => q (Fin.castAdd m a) 0) *
          η₂ (fun b => q (Fin.natAdd n b) 0) *
          F (section43QSpatial (d := d) (n := n + m) q) =
      (η₁.conj (splitFirst n m (fun c => q c 0)) *
          η₂ (splitLast n m (fun c => q c 0))) *
        F
          ((axisPairBlockGlobalSpatialCLE (d := d) n m).symm
            (axisPairBlockGlobalSpatialCLE (d := d) n m
              (section43QSpatial (d := d) (n := n + m) q)))
  rw [(axisPairBlockGlobalSpatialCLE
    (d := d) n m).symm_apply_apply]
  rfl

/-- The split block-global spatial chart conjugated to the common absolute
`k + 1` particle coordinates. -/
noncomputable def generatorSplitGlobalSpatialCLE
    (i : GeneratorIndex k) :
    Section43SpatialSpace d (k + 1) ≃L[ℝ]
      Section43SpatialSpace d (k + 1) :=
  (generatorSplitToAbsoluteSpatialCLE (d := d) i).symm |>.trans
    ((axisPairBlockGlobalSpatialCLE
      (d := d) i.n i.m).trans
        (generatorSplitToAbsoluteSpatialCLE (d := d) i))

/-- The common-arity spatial pullback appearing in the corrected generator
source normal form. -/
noncomputable def generatorSplitGlobalSpatialPullbackCLM
    (i : GeneratorIndex k) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (generatorSplitGlobalSpatialCLE (d := d) i).symm

/-- The inverse spatial pullback. Applying this before Hermite expansion
ensures that the block-global chart sends the finite shell back toward the
original common spatial test. -/
noncomputable def generatorSplitGlobalSpatialPushforwardCLM
    (i : GeneratorIndex k) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (generatorSplitGlobalSpatialCLE (d := d) i)

@[simp] theorem generatorSplitGlobalSpatialPullbackCLM_pushforward
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    generatorSplitGlobalSpatialPullbackCLM (d := d) i
        (generatorSplitGlobalSpatialPushforwardCLM (d := d) i F) =
      F := by
  ext η
  simp [generatorSplitGlobalSpatialPullbackCLM,
    generatorSplitGlobalSpatialPushforwardCLM]

@[simp] theorem generatorSplitGlobalSpatialPushforwardCLM_pullback
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    generatorSplitGlobalSpatialPushforwardCLM (d := d) i
        (generatorSplitGlobalSpatialPullbackCLM (d := d) i F) =
      F := by
  ext η
  simp [generatorSplitGlobalSpatialPullbackCLM,
    generatorSplitGlobalSpatialPushforwardCLM]

/-- Hermite coefficient extraction in the separate block-global spatial
chart. These are the coefficients that cancel the split-dependent spatial
pullback in the finite source identity. -/
noncomputable def generatorSplitGlobalSpatialCoefficientCLM
    (i : GeneratorIndex k)
    (m : ℕ) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ] ℂ :=
  (complexSpatialHermiteCoefficientCLM
    d (k + 1) (Nat.succ_pos k) m).comp
      (generatorSplitGlobalSpatialPushforwardCLM (d := d) i)

end GeneratorHermiteHilbertFieldFamilyData
end OSIIChapterV
end OSReconstruction
