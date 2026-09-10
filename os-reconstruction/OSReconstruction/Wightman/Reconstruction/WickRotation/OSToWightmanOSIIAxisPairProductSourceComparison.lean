/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent














noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

/-- Reverse the left point block and fix the right point block. -/
def osiiAxisPairLeftBlockReversePerm
    (n m : ℕ) : Equiv.Perm (Fin (n + m)) :=
  (finSumFinEquiv (m := n) (n := m)).symm.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin m))).trans
      (finSumFinEquiv (m := n) (n := m)))

@[simp] theorem osiiAxisPairLeftBlockReversePerm_castAdd
    (n m : ℕ) (i : Fin n) :
    osiiAxisPairLeftBlockReversePerm n m (Fin.castAdd m i) =
      Fin.castAdd m (Fin.rev i) := by
  simp [osiiAxisPairLeftBlockReversePerm]

@[simp] theorem osiiAxisPairLeftBlockReversePerm_natAdd
    (n m : ℕ) (j : Fin m) :
    osiiAxisPairLeftBlockReversePerm n m (Fin.natAdd n j) =
      Fin.natAdd n j := by
  simp [osiiAxisPairLeftBlockReversePerm]

private def osiiAxisPairNPointAppendLinearEquiv
    (d n m : ℕ) :
    (NPointDomain d n × NPointDomain d m) ≃ₗ[ℝ]
      NPointDomain d (n + m) :=
  { Fin.appendEquiv n m with
    map_add' := by
      intro x y
      apply (Fin.appendEquiv n m).symm.injective
      ext i <;> simp [Fin.appendEquiv]
    map_smul' := by
      intro c x
      apply (Fin.appendEquiv n m).symm.injective
      ext i <;> simp [Fin.appendEquiv] }

/-- Continuous linear append equivalence for two finite spacetime blocks. -/
noncomputable def osiiAxisPairNPointAppendCLE
    (d n m : ℕ) :
    (NPointDomain d n × NPointDomain d m) ≃L[ℝ]
      NPointDomain d (n + m) :=
  (osiiAxisPairNPointAppendLinearEquiv d n m).toContinuousLinearEquiv

@[simp] theorem osiiAxisPairNPointAppendCLE_apply_left
    (d n m : ℕ) (p : NPointDomain d n × NPointDomain d m)
    (i : Fin n) :
    osiiAxisPairNPointAppendCLE d n m p (Fin.castAdd m i) = p.1 i := by
  simp [osiiAxisPairNPointAppendCLE, osiiAxisPairNPointAppendLinearEquiv]

@[simp] theorem osiiAxisPairNPointAppendCLE_apply_right
    (d n m : ℕ) (p : NPointDomain d n × NPointDomain d m)
    (j : Fin m) :
    osiiAxisPairNPointAppendCLE d n m p (Fin.natAdd n j) = p.2 j := by
  simp [osiiAxisPairNPointAppendCLE, osiiAxisPairNPointAppendLinearEquiv]

@[simp] theorem osiiAxisPairNPointAppendCLE_symm_fst_apply
    (d n m : ℕ) (x : NPointDomain d (n + m)) (i : Fin n) :
    ((osiiAxisPairNPointAppendCLE d n m).symm x).1 i =
      splitFirst n m x i := by
  have h := congrFun
    ((osiiAxisPairNPointAppendCLE d n m).apply_symm_apply x)
    (Fin.castAdd m i)
  simpa [splitFirst] using h

@[simp] theorem osiiAxisPairNPointAppendCLE_symm_snd_apply
    (d n m : ℕ) (x : NPointDomain d (n + m)) (j : Fin m) :
    ((osiiAxisPairNPointAppendCLE d n m).symm x).2 j =
      splitLast n m x j := by
  have h := congrFun
    ((osiiAxisPairNPointAppendCLE d n m).apply_symm_apply x)
    (Fin.natAdd n j)
  simpa [splitLast] using h

private def osiiAxisPairTimeReflectionLinearEquiv
    (d : ℕ) : SpacetimeDim d ≃ₗ[ℝ] SpacetimeDim d :=
  { toFun := timeReflection d
    invFun := timeReflection d
    left_inv := by
      intro x
      ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [timeReflection]
      · simp [timeReflection, hμ]
    right_inv := by
      intro x
      ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [timeReflection]
      · simp [timeReflection, hμ]
    map_add' := by
      intro x y
      ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [timeReflection]
        ring
      · simp [timeReflection, hμ]
    map_smul' := by
      intro c x
      ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [timeReflection]
      · simp [timeReflection, hμ] }

/-- Time reflection as a continuous real-linear involution of spacetime. -/
noncomputable def osiiAxisPairTimeReflectionCLE
    (d : ℕ) : SpacetimeDim d ≃L[ℝ] SpacetimeDim d :=
  (osiiAxisPairTimeReflectionLinearEquiv d).toContinuousLinearEquiv

@[simp] theorem osiiAxisPairTimeReflectionCLE_apply
    (d : ℕ) (x : SpacetimeDim d) :
    osiiAxisPairTimeReflectionCLE d x = timeReflection d x := rfl

/-- Apply difference coordinates separately to the two spacetime blocks. -/
noncomputable def osiiAxisPairBlockwiseSpacetimeDiffCLE
    (d n m : ℕ) :
    NPointDomain d (n + m) ≃L[ℝ] NPointDomain d (n + m) :=
  (osiiAxisPairNPointAppendCLE d n m).symm |>.trans
    ((ContinuousLinearEquiv.prodCongr
      (section43DiffCoordRealCLE d n)
      (section43DiffCoordRealCLE d m)).trans
        (osiiAxisPairNPointAppendCLE d n m))

@[simp] theorem osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_left
    (d n m : ℕ) (x : NPointDomain d (n + m)) (i : Fin n) :
    osiiAxisPairBlockwiseSpacetimeDiffCLE d n m x (Fin.castAdd m i) =
      section43DiffCoordRealCLE d n (splitFirst n m x) i := by
  rw [osiiAxisPairBlockwiseSpacetimeDiffCLE]
  simp only [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,
    osiiAxisPairNPointAppendCLE_apply_left]
  have hsplit :
      ((osiiAxisPairNPointAppendCLE d n m).symm x).1 =
        splitFirst n m x := by
    funext k
    exact osiiAxisPairNPointAppendCLE_symm_fst_apply d n m x k
  rw [hsplit]

@[simp] theorem osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_right
    (d n m : ℕ) (x : NPointDomain d (n + m)) (j : Fin m) :
    osiiAxisPairBlockwiseSpacetimeDiffCLE d n m x (Fin.natAdd n j) =
      section43DiffCoordRealCLE d m (splitLast n m x) j := by
  rw [osiiAxisPairBlockwiseSpacetimeDiffCLE]
  simp only [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply,
    osiiAxisPairNPointAppendCLE_apply_right]
  have hsplit :
      ((osiiAxisPairNPointAppendCLE d n m).symm x).2 =
        splitLast n m x := by
    funext k
    exact osiiAxisPairNPointAppendCLE_symm_snd_apply d n m x k
  rw [hsplit]

@[simp] theorem osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left
    (d n m : ℕ) (q : NPointDomain d (n + m)) (i : Fin n) :
    (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q
        (Fin.castAdd m i) =
      (section43DiffCoordRealCLE d n).symm
        (splitFirst n m q) i := by
  have h :
      splitFirst n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q) =
        (section43DiffCoordRealCLE d n).symm
          (splitFirst n m q) := by
    apply (section43DiffCoordRealCLE d n).injective
    ext k μ
    rw [(section43DiffCoordRealCLE d n).apply_symm_apply]
    calc
      section43DiffCoordRealCLE d n
          (splitFirst n m
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)) k μ =
          osiiAxisPairBlockwiseSpacetimeDiffCLE d n m
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)
            (Fin.castAdd m k) μ := by
              rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_left]
      _ = q (Fin.castAdd m k) μ := by
        exact congrArg (fun z : SpacetimeDim d => z μ)
          (congrFun
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).apply_symm_apply q)
            (Fin.castAdd m k))
      _ = splitFirst n m q k μ := rfl
  exact congrFun h i

@[simp] theorem osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right
    (d n m : ℕ) (q : NPointDomain d (n + m)) (j : Fin m) :
    (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q
        (Fin.natAdd n j) =
      (section43DiffCoordRealCLE d m).symm
        (splitLast n m q) j := by
  have h :
      splitLast n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q) =
        (section43DiffCoordRealCLE d m).symm
          (splitLast n m q) := by
    apply (section43DiffCoordRealCLE d m).injective
    ext k μ
    rw [(section43DiffCoordRealCLE d m).apply_symm_apply]
    calc
      section43DiffCoordRealCLE d m
          (splitLast n m
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)) k μ =
          osiiAxisPairBlockwiseSpacetimeDiffCLE d n m
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q)
            (Fin.natAdd n k) μ := by
              rw [osiiAxisPairBlockwiseSpacetimeDiffCLE_apply_right]
      _ = q (Fin.natAdd n k) μ := by
        exact congrArg (fun z : SpacetimeDim d => z μ)
          (congrFun
            ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).apply_symm_apply q)
            (Fin.natAdd n k))
      _ = splitLast n m q k μ := rfl
  exact congrFun h j

/-- Reverse the left point order and time-reflect that block, fixing the right
block. -/
noncomputable def osiiAxisPairReflectReverseLeftSpacetimeCLE
    (d n m : ℕ) :
    NPointDomain d (n + m) ≃L[ℝ] NPointDomain d (n + m) :=
  (osiiAxisPairNPointAppendCLE d n m).symm |>.trans
    ((ContinuousLinearEquiv.prodCongr
      ((LinearEquiv.funCongrLeft ℝ (SpacetimeDim d) Fin.revPerm
        ).toContinuousLinearEquiv.trans
          (ContinuousLinearEquiv.piCongrRight
            (fun _ : Fin n => osiiAxisPairTimeReflectionCLE d)))
      (ContinuousLinearEquiv.refl ℝ (NPointDomain d m))).trans
        (osiiAxisPairNPointAppendCLE d n m))

@[simp] theorem osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_left
    (d n m : ℕ) (x : NPointDomain d (n + m)) (i : Fin n) :
    osiiAxisPairReflectReverseLeftSpacetimeCLE d n m x
        (Fin.castAdd m i) =
      timeReflection d (x (Fin.castAdd m (Fin.rev i))) := by
  simp [osiiAxisPairReflectReverseLeftSpacetimeCLE,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, splitFirst]

@[simp] theorem osiiAxisPairReflectReverseLeftSpacetimeCLE_apply_right
    (d n m : ℕ) (x : NPointDomain d (n + m)) (j : Fin m) :
    osiiAxisPairReflectReverseLeftSpacetimeCLE d n m x
        (Fin.natAdd n j) =
      x (Fin.natAdd n j) := by
  simp [osiiAxisPairReflectReverseLeftSpacetimeCLE, splitLast]

/-- Linear part of the two-block-to-global spacetime difference chart. -/
noncomputable def osiiAxisPairBlockGlobalSpacetimeCLE
    (d n m : ℕ) :
    NPointDomain d (n + m) ≃L[ℝ] NPointDomain d (n + m) :=
  (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm |>.trans
    ((osiiAxisPairReflectReverseLeftSpacetimeCLE d n m).trans
      (section43DiffCoordRealCLE d (n + m)))

/-- Absolute spacetime translation used after reflecting the left block and
shifting the right block. -/
def osiiAxisPairGlobalAbsoluteSpacetimeShift
    (d n m : ℕ) (s t : ℝ) : NPointDomain d (n + m) :=
  fun k => timeShiftVec d
    (osiiAxisPairGlobalAbsoluteTimeShift n m s t k)

/-- The affine displacement in global spacetime difference coordinates. -/
def osiiAxisPairGlobalSpacetimeDiffShift
    (d n m : ℕ) (s t : ℝ) : NPointDomain d (n + m) :=
  section43DiffCoordRealCLE d (n + m)
    (osiiAxisPairGlobalAbsoluteSpacetimeShift d n m s t)

/-- The global absolute spacetime configuration associated to separate
left/right difference coordinates. -/
def osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m)) :
    NPointDomain d (n + m) :=
  osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
      ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q) +
    osiiAxisPairGlobalAbsoluteSpacetimeShift d n m s t

@[simp] theorem osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_left
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m))
    (i : Fin n) :
    osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q
        (Fin.castAdd m i) =
      timeReflection d
          ((section43DiffCoordRealCLE d n).symm
            (splitFirst n m q) (Fin.rev i)) +
        timeShiftVec d s := by
  simp [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig,
    osiiAxisPairGlobalAbsoluteSpacetimeShift,
    osiiAxisPairGlobalAbsoluteTimeShift]

@[simp] theorem osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_right
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m))
    (j : Fin m) :
    osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q
        (Fin.natAdd n j) =
      (section43DiffCoordRealCLE d m).symm
          (splitLast n m q) j +
        timeShiftVec d (s + t) := by
  simp [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig,
    osiiAxisPairGlobalAbsoluteSpacetimeShift,
    osiiAxisPairGlobalAbsoluteTimeShift]

/-- The time projection of the spacetime absolute configuration is the scalar
absolute-time configuration from the support geometry. -/
theorem osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_time
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m)) :
    (fun k =>
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q k 0) =
      osiiAxisPairBlockGlobalAbsoluteTimeConfig n m s t
        (fun k => q k 0) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_left,
      osiiAxisPairBlockGlobalAbsoluteTimeConfig_left]
    simp [section43ScalarDiffCLE_symm_apply, splitFirst, timeReflection,
      timeShiftVec]
  · intro j
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_right,
      osiiAxisPairBlockGlobalAbsoluteTimeConfig_right]
    simp [section43ScalarDiffCLE_symm_apply, splitLast, timeShiftVec]

/-- Affine two-block-to-global spacetime difference map. -/
def osiiAxisPairBlockGlobalSpacetimeAffine
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m)) :
    NPointDomain d (n + m) :=
  osiiAxisPairBlockGlobalSpacetimeCLE d n m q +
    osiiAxisPairGlobalSpacetimeDiffShift d n m s t

/-- The affine spacetime chart is exactly the global difference chart of the
reflected, reversed, and shifted absolute configuration. -/
theorem section43DiffCoordRealCLE_blockGlobalAbsoluteSpacetimeConfig
    (d n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m)) :
    section43DiffCoordRealCLE d (n + m)
        (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q) =
      osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q := by
  rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig, map_add]
  rfl

/-- The time projection of the full spacetime affine chart is the scalar affine
chart used to transport the cutoff. -/
theorem osiiAxisPairBlockGlobalSpacetimeAffine_time
    (d n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (s t : ℝ) (q : NPointDomain d (n + m)) :
    (fun k => osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q k 0) =
      osiiAxisPairBlockGlobalTimeAffine n m s t
        (fun k => q k 0) := by
  rw [← section43DiffCoordRealCLE_blockGlobalAbsoluteSpacetimeConfig]
  rw [← section43ScalarDiffCLE_blockGlobalAbsoluteTimeConfig
    n m hn hm s t (fun k => q k 0)]
  funext k
  rw [section43DiffCoordRealCLE_apply, section43ScalarDiffCLE_apply]
  split_ifs with hk
  · exact congrFun
      (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_time
        d n m s t q) k
  · have htime :=
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_time
        d n m s t q
    rw [congrFun htime k,
      congrFun htime ⟨k.val - 1, by omega⟩]

/-- Pull a block-chart Schwartz test forward to the global affine difference
chart.  Pointwise this is `F(q ↦ A⁻¹(q - b))`. -/
noncomputable def osiiAxisPairBlockGlobalSpacetimePullbackCLM
    (d n m : ℕ) (s t : ℝ) :
    SchwartzNPoint d (n + m) →L[ℂ] SchwartzNPoint d (n + m) :=
  (SchwartzMap.compSubConstCLM ℂ
      (osiiAxisPairGlobalSpacetimeDiffShift d n m s t)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm)

@[simp] theorem osiiAxisPairBlockGlobalSpacetimePullbackCLM_apply
    (d n m : ℕ) (s t : ℝ)
    (F : SchwartzNPoint d (n + m))
    (q : NPointDomain d (n + m)) :
    osiiAxisPairBlockGlobalSpacetimePullbackCLM d n m s t F q =
      F ((osiiAxisPairBlockGlobalSpacetimeCLE d n m).symm
        (q - osiiAxisPairGlobalSpacetimeDiffShift d n m s t)) := by
  rfl

@[simp] theorem osiiAxisPairBlockGlobalSpacetimePullbackCLM_affine
    (d n m : ℕ) (s t : ℝ)
    (F : SchwartzNPoint d (n + m))
    (q : NPointDomain d (n + m)) :
    osiiAxisPairBlockGlobalSpacetimePullbackCLM d n m s t F
        (osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q) =
      F q := by
  simp [osiiAxisPairBlockGlobalSpacetimeAffine,
    osiiAxisPairBlockGlobalSpacetimePullbackCLM_apply]

variable {d : ℕ} [NeZero d]

@[simp] theorem tsupport_schwartzMap_conj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : SchwartzMap E ℂ) :
    tsupport ((η.conj : SchwartzMap E ℂ) : E → ℂ) =
      tsupport (η : E → ℂ) := by
  have hsupp :
      Function.support ((η.conj : SchwartzMap E ℂ) : E → ℂ) =
        Function.support (η : E → ℂ) := by
    ext x
    simp [Function.mem_support, SchwartzMap.conj_apply]
  simp [tsupport, hsupp]

theorem hasCompactSupport_schwartzMap_conj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : SchwartzMap E ℂ)
    (hη : HasCompactSupport (η : E → ℂ)) :
    HasCompactSupport ((η.conj : SchwartzMap E ℂ) : E → ℂ) := by
  simpa [HasCompactSupport] using hη

omit [NeZero d] in
/-- Changing the common shift translates every absolute spacetime point by
the same Euclidean time vector. -/
theorem osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_commonShift
    (n m : ℕ) (s t : ℝ) (q : NPointDomain d (n + m)) :
    osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q =
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m 0 t q +
        fun _ => timeShiftVec d s := by
  ext k μ
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [Pi.add_apply]
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_left,
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_left]
    simp [timeShiftVec]
  · intro j
    simp only [Pi.add_apply]
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_right,
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_right]
    by_cases hμ : μ = 0
    · subst μ
      simp [timeShiftVec]
      ring
    · simp [timeShiftVec, hμ]

omit [NeZero d] in
/-- The zero-common-shift absolute block chart covers every configuration. -/
theorem osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_surjective
    (n m : ℕ) (t : ℝ) :
    Function.Surjective
      (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m 0 t) := by
  intro x
  let b := osiiAxisPairGlobalAbsoluteSpacetimeShift d n m 0 t
  let q :=
    osiiAxisPairBlockwiseSpacetimeDiffCLE d n m
      ((osiiAxisPairReflectReverseLeftSpacetimeCLE d n m).symm (x - b))
  refine ⟨q, ?_⟩
  simp [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig, q, b]

end OSReconstruction
