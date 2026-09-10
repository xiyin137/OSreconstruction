import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSourceComparison

/-!
# OS-II Chapter V absolute-spatial generator source

This file turns the affine global source comparison into a continuous
Schwinger functional of an arbitrary full spatial Schwartz test.

The compact left/right time profiles are combined in the separate-coordinate
chart. A sufficiently large common time shift transports their support into
the global strict-positive difference-time orthant, so every spatial test
lands honestly in the zero-diagonal OS test space. The construction is then
reindexed to the common `k + 1` absolute-spatial space of the generator
Hermite expansion.

No split-independence is asserted here. The final common-edge input must prove
that the resulting split-induced functionals agree; this module proves that
each concrete reflected Hermite mode is represented by its corresponding
split-induced functional.
-/

noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

private theorem twoBlockProductSchwartz_apply_split
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin (n + m) → ℝ) :
    SCV.twoBlockProductSchwartz η₁ η₂ x =
      η₁ (splitFirst n m x) * η₂ (splitLast n m x) := by
  have hx :
      x = Fin.append (splitFirst n m x) (splitLast n m x) := by
    ext c
    refine Fin.addCases ?_ ?_ c
    · intro i
      simp [splitFirst, Fin.append_left]
    · intro j
      simp [splitLast, Fin.append_right]
  rw [hx]
  simp [SCV.twoBlockProductSchwartz_apply]

private theorem twoBlockProductSchwartz_tsupport_subset
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ) :
    tsupport (SCV.twoBlockProductSchwartz η₁ η₂ :
        (Fin (n + m) → ℝ) → ℂ) ⊆
      (splitFirst n m) ⁻¹' tsupport (η₁ : (Fin n → ℝ) → ℂ) ∩
        (splitLast n m) ⁻¹' tsupport (η₂ : (Fin m → ℝ) → ℂ) := by
  refine closure_minimal ?_ <|
    ((isClosed_tsupport _).preimage (splitFirst_continuousLinear n m)).inter
      ((isClosed_tsupport _).preimage (splitLast_continuousLinear n m))
  intro x hx
  have hxne :
      η₁ (splitFirst n m x) * η₂ (splitLast n m x) ≠ 0 := by
    simpa [Function.mem_support, twoBlockProductSchwartz_apply_split] using hx
  constructor
  · apply subset_tsupport
    simpa [Function.mem_support] using
      (fun hzero => hxne (by simp [hzero]))
  · apply subset_tsupport
    simpa [Function.mem_support] using
      (fun hzero => hxne (by simp [hzero]))

/-- One full-arity separate-coordinate source with arbitrary spatial test and
the reflected-left/right compact time factors. -/
noncomputable def axisPairSeparateTimeSpatialTensor
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    SchwartzNPoint d (n + m) :=
  section43NPointTimeSpatialTensor d (n + m)
    (SCV.twoBlockProductSchwartz η₁.conj η₂) F

/-- The separate-coordinate source, continuous and linear in its common
spatial Schwartz factor. This is the source fed into the native axis-pair
semigroup before its block-global affine pullback is applied. -/
noncomputable def axisPairSeparateTimeSpatialTensorCLM
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ]
      SchwartzNPoint d (n + m) :=
  section43TimeSpatialTensorSpatialCLM d (n + m)
    (SCV.twoBlockProductSchwartz η₁.conj η₂)

@[simp] theorem axisPairSeparateTimeSpatialTensorCLM_apply
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    axisPairSeparateTimeSpatialTensorCLM n m η₁ η₂ F =
      axisPairSeparateTimeSpatialTensor n m η₁ η₂ F := rfl

/-- The affine global source, continuous and linear in an arbitrary common
spatial Schwartz test. -/
noncomputable def axisPairGlobalAbsoluteSpatialSourceCLM
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ]
      SchwartzNPoint d (n + m) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d (n + m))).comp
      ((osiiAxisPairBlockGlobalSpacetimePullbackCLM d n m s t).comp
        (section43TimeSpatialTensorSpatialCLM d (n + m)
          (SCV.twoBlockProductSchwartz η₁.conj η₂)))

@[simp] theorem axisPairGlobalAbsoluteSpatialSourceCLM_apply
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    axisPairGlobalAbsoluteSpatialSourceCLM
        n m η₁ η₂ s t F =
      axisPairGlobalTimeSpatialSource n m s t
        (axisPairSeparateTimeSpatialTensor n m η₁ η₂ F) := by
  rfl

@[simp] theorem axisPairGlobalAbsoluteSpatialSourceCLM_config
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ)
    (q : NPointDomain d (n + m)) :
    axisPairGlobalAbsoluteSpatialSourceCLM n m η₁ η₂ s t F
        (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q) =
      η₁.conj (fun i => q (Fin.castAdd m i) 0) *
        η₂ (fun j => q (Fin.natAdd n j) 0) *
        F (section43QSpatial (d := d) (n := n + m) q) := by
  have hleft :
      splitFirst n m (fun c => q c 0) =
        fun i => q (Fin.castAdd m i) 0 := rfl
  have hright :
      splitLast n m (fun c => q c 0) =
        fun j => q (Fin.natAdd n j) 0 := rfl
  rw [axisPairGlobalAbsoluteSpatialSourceCLM_apply,
    axisPairGlobalTimeSpatialSource_config]
  simp [axisPairSeparateTimeSpatialTensor,
    section43NPointTimeSpatialTensor_apply,
    twoBlockProductSchwartz_apply_split, section43QTime,
    nPointTimeSpatialCLE, hleft, hright]

/-- Once the common shift places the transported time support in the global
strict-positive orthant, every member of the spatial source family is
supported in the ordered Euclidean region. -/
theorem axisPairGlobalAbsoluteSpatialSourceCLM_tsupport_subset_orderedPositive
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    tsupport
        ((axisPairGlobalAbsoluteSpatialSourceCLM
          n m η₁ η₂ s t F : SchwartzNPoint d (n + m)) :
            NPointDomain d (n + m) → ℂ) ⊆
      OrderedPositiveTimeRegion d (n + m) := by
  intro x hx
  let e := osiiAxisPairBlockGlobalSpacetimeCLE d n m
  let b := osiiAxisPairGlobalSpacetimeDiffShift d n m s t
  let product := SCV.twoBlockProductSchwartz η₁.conj η₂
  let G := section43NPointTimeSpatialTensor d (n + m) product F
  have hx_diff :
      section43DiffCoordRealCLE d (n + m) x ∈
        tsupport
          ((osiiAxisPairBlockGlobalSpacetimePullbackCLM
            d n m s t G : SchwartzNPoint d (n + m)) :
              NPointDomain d (n + m) → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((osiiAxisPairBlockGlobalSpacetimePullbackCLM
          d n m s t G : SchwartzNPoint d (n + m)) :
            NPointDomain d (n + m) → ℂ)
        (section43DiffCoordRealCLE d (n + m)).continuous
        (by
          simpa [axisPairGlobalAbsoluteSpatialSourceCLM,
            axisPairSeparateTimeSpatialTensor, product, G] using hx)
  let q := e.symm (section43DiffCoordRealCLE d (n + m) x - b)
  have hmap :
      Continuous (fun z : NPointDomain d (n + m) => e.symm (z - b)) :=
    e.symm.continuous.comp (continuous_id.sub continuous_const)
  have hq : q ∈ tsupport (G : NPointDomain d (n + m) → ℂ) := by
    have hpull :
        ((osiiAxisPairBlockGlobalSpacetimePullbackCLM
          d n m s t G : SchwartzNPoint d (n + m)) :
            NPointDomain d (n + m) → ℂ) =
          fun z => G (e.symm (z - b)) := by
      funext z
      simp [e, b,
        osiiAxisPairBlockGlobalSpacetimePullbackCLM_apply]
    rw [hpull] at hx_diff
    have hpre :=
      tsupport_comp_subset_preimage
        (G : NPointDomain d (n + m) → ℂ) hmap hx_diff
    simpa [q] using hpre
  let δ := section43QTime (d := d) (n := n + m) q
  have hδ_product :
      δ ∈ tsupport (product : (Fin (n + m) → ℝ) → ℂ) := by
    exact
      tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d (n + m) product F (by simpa [G] using hq)
  have hparts :=
    twoBlockProductSchwartz_tsupport_subset
      n m η₁.conj η₂ (by simpa [product] using hδ_product)
  have hleft :
      splitFirst n m δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ) := by
    simpa using hparts.1
  have hright :
      splitLast n m δ ∈ tsupport (η₂ : (Fin m → ℝ) → ℂ) :=
    hparts.2
  have hδ_pos :
      osiiAxisPairBlockGlobalTimeAffine n m s t δ ∈
        section43TimeStrictPositiveRegion (n + m) :=
    osiiAxisPairBlockGlobalTimeAffine_mem_strictPositive
      n m hn hm s t ht δ (hη₁ hleft) (hη₂ hright)
        (hspan _ hleft)
  have hx_affine :
      section43DiffCoordRealCLE d (n + m) x =
        osiiAxisPairBlockGlobalSpacetimeAffine d n m s t q := by
    simp [q, e, b, osiiAxisPairBlockGlobalSpacetimeAffine]
  have hx_time_pos :
      ∀ c : Fin (n + m),
        0 < section43DiffCoordRealCLE d (n + m) x c 0 := by
    intro c
    rw [hx_affine]
    have htime :=
      congrFun
        (osiiAxisPairBlockGlobalSpacetimeAffine_time
          d n m hn hm s t q) c
    rw [htime]
    exact hδ_pos c
  have hordered :=
    section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
      d (n + m) hx_time_pos
  simpa using hordered

/-- The affine global spatial family as an honest continuous linear map into
the zero-diagonal OS test space. -/
noncomputable def axisPairGlobalAbsoluteSpatialSourceZeroCLM
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + m) :=
  (axisPairGlobalAbsoluteSpatialSourceCLM
    (d := d) n m η₁ η₂ s t).codRestrict
      (zeroDiagonalSubmodule d (n + m))
      (fun F => by
        change VanishesToInfiniteOrderOnCoincidence _
        exact
          VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
            (axisPairGlobalAbsoluteSpatialSourceCLM n m η₁ η₂ s t F)
            (axisPairGlobalAbsoluteSpatialSourceCLM_tsupport_subset_orderedPositive
              n m hn hm η₁ hη₁ η₂ hη₂ s t ht hspan F))

@[simp] theorem axisPairGlobalAbsoluteSpatialSourceZeroCLM_coe
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    (axisPairGlobalAbsoluteSpatialSourceZeroCLM
      n m hn hm η₁ hη₁ η₂ hη₂ s t ht hspan F).1 =
      axisPairGlobalAbsoluteSpatialSourceCLM n m η₁ η₂ s t F := rfl

/-- The induced Schwinger functional on the full spatial Schwartz space. -/
noncomputable def axisPairGlobalAbsoluteSpatialSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp
    (axisPairGlobalAbsoluteSpatialSourceZeroCLM
      n m hn hm η₁ hη₁ η₂ hη₂ s t ht hspan)

@[simp] theorem axisPairGlobalAbsoluteSpatialSchwingerCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin n → ℝ) → ℂ),
      (section43ScalarDiffCLE n).symm δ (Fin.rev ⟨0, hn⟩) < s)
    (F : SchwartzMap (Section43SpatialSpace d (n + m)) ℂ) :
    axisPairGlobalAbsoluteSpatialSchwingerCLM
        OS n m hn hm η₁ hη₁ η₂ hη₂ s t ht hspan F =
      OS.S (n + m)
        (axisPairGlobalAbsoluteSpatialSourceZeroCLM
          n m hn hm η₁ hη₁ η₂ hη₂ s t ht hspan F) := rfl

/-- Reindex a split's concatenated spatial coordinates by the common
`k + 1` absolute-particle cardinality. -/
noncomputable def generatorSplitToAbsoluteSpatialCLE
    {k : ℕ} (i : GeneratorIndex k) :
    Section43SpatialSpace d (i.n + i.m) ≃L[ℝ]
      Section43SpatialSpace d (k + 1) :=
  (section43SpatialParticleCLE d (i.n + i.m)).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin (k + 1) => Fin d → ℝ)
      (finCongr i.absoluteCard_eq.symm)).trans
        (section43SpatialParticleCLE d (k + 1)).symm)

omit [NeZero d] in
@[simp] theorem generatorSplitToAbsoluteSpatialCLE_apply
    {k : ℕ} (i : GeneratorIndex k)
    (η : Section43SpatialSpace d (i.n + i.m))
    (c : Fin (k + 1)) (j : Fin d) :
    section43SpatialParticleCLE d (k + 1)
        (generatorSplitToAbsoluteSpatialCLE i η) c j =
      section43SpatialParticleCLE d (i.n + i.m) η
        (Fin.cast i.absoluteCard_eq c) j := by
  rfl

/-- The common absolute Hermite vector expressed in a split's concatenated
spatial coordinate presentation. -/
noncomputable def generatorSplitSpatialHermite
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ) :
    SchwartzMap (Section43SpatialSpace d (i.n + i.m)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (generatorSplitToAbsoluteSpatialCLE i)
    (spatialHermite d (k + 1) (Nat.succ_pos k) r)

@[simp] theorem generatorSplitSpatialHermite_apply
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ)
    (η : Section43SpatialSpace d (i.n + i.m)) :
    generatorSplitSpatialHermite i r η =
      spatialHermite d (k + 1) (Nat.succ_pos k) r
        ((section43SpatialParticleCLE d (k + 1)).symm
          (fun c j =>
            section43SpatialParticleCLE d (i.n + i.m) η
              (Fin.cast i.absoluteCard_eq c) j)) := by
  rw [generatorSplitSpatialHermite,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change
    spatialHermite d (k + 1) (Nat.succ_pos k) r
        (generatorSplitToAbsoluteSpatialCLE i η) =
      spatialHermite d (k + 1) (Nat.succ_pos k) r
        ((section43SpatialParticleCLE d (k + 1)).symm
          (fun c j =>
            section43SpatialParticleCLE d (i.n + i.m) η
              (Fin.cast i.absoluteCard_eq c) j))
  have harg :
      generatorSplitToAbsoluteSpatialCLE i η =
        (section43SpatialParticleCLE d (k + 1)).symm
          (fun c j =>
            section43SpatialParticleCLE d (i.n + i.m) η
              (Fin.cast i.absoluteCard_eq c) j) := by
    apply (section43SpatialParticleCLE d (k + 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext c j
    exact generatorSplitToAbsoluteSpatialCLE_apply i η c j
  rw [harg]

/-- On every absolute Hermite basis vector, the one-piece spatial family is
exactly the existing product of left/right generator blocks. -/
theorem axisPairSeparateTimeSpatialTensor_generatorHermite
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ)
    (η₁ : SchwartzMap (Fin i.n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin i.m → ℝ) ℂ) :
    axisPairSeparateTimeSpatialTensor i.n i.m η₁ η₂
        (generatorSplitSpatialHermite i r) =
      axisPairBlockTimeSpatialTensor i.n i.m
        η₁ (leftSpatialHermiteBlock d i r)
        η₂ (rightSpatialHermiteBlock d i r) := by
  ext q
  rw [axisPairBlockTimeSpatialTensor_generatorHermite_apply]
  simp only [axisPairSeparateTimeSpatialTensor,
    section43NPointTimeSpatialTensor_apply,
    twoBlockProductSchwartz_apply_split,
    SchwartzMap.conj_apply]
  have hleft :
      splitFirst i.n i.m
          (section43QTime (d := d) (n := i.n + i.m) q) =
        section43QTime (d := d) (n := i.n)
          (section43LeftBlock d i.n i.m q) := by
    rfl
  have hright :
      splitLast i.n i.m
          (section43QTime (d := d) (n := i.n + i.m) q) =
        section43QTime (d := d) (n := i.m)
          (section43RightTailBlock d i.n i.m q) := by
    rfl
  rw [hleft, hright, generatorSplitSpatialHermite_apply]
  congr 2

/-- Pull a common absolute spatial test into a split's concatenated spatial
coordinate presentation. -/
noncomputable def generatorSplitSpatialPullbackCLM
    {k : ℕ} (i : GeneratorIndex k) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d (i.n + i.m)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (generatorSplitToAbsoluteSpatialCLE i)

@[simp] theorem generatorSplitSpatialPullbackCLM_hermite
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ) :
    generatorSplitSpatialPullbackCLM i
        (spatialHermite d (k + 1) (Nat.succ_pos k) r) =
      generatorSplitSpatialHermite i r := rfl

/-- The split-induced Schwinger functional, expressed on the common
`k + 1` absolute-spatial Schwartz space. -/
noncomputable def generatorSplitAbsoluteSpatialSchwingerCLM
    (OS : OsterwalderSchraderAxioms d)
    {k : ℕ} (i : GeneratorIndex k)
    (η₁ : SchwartzMap (Fin i.n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin i.n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.n)
    (η₂ : SchwartzMap (Fin i.m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin i.m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.m)
    (s t : ℝ) (ht : 0 ≤ t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin i.n → ℝ) → ℂ),
      (section43ScalarDiffCLE i.n).symm δ
        (Fin.rev ⟨0, i.hn⟩) < s) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →L[ℂ] ℂ :=
  (axisPairGlobalAbsoluteSpatialSchwingerCLM
    OS i.n i.m i.hn i.hm η₁ hη₁ η₂ hη₂ s t ht hspan).comp
      (generatorSplitSpatialPullbackCLM i)

/-- Every concrete reflected two-block Hermite source is represented by the
corresponding split-induced continuous functional on the common absolute
spatial Hermite vector. -/
theorem axisPairTwoBlockTimeSpatialSource_schwinger_eq_absoluteHermite
    (OS : OsterwalderSchraderAxioms d)
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ)
    (η₁ : SchwartzMap (Fin i.n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin i.n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.n)
    (η₂ : SchwartzMap (Fin i.m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin i.m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion i.m)
    (s t : ℝ) (ht : 0 < t)
    (hspan : ∀ δ ∈ tsupport (η₁ : (Fin i.n → ℝ) → ℂ),
      (section43ScalarDiffCLE i.n).symm δ
        (Fin.rev ⟨0, i.hn⟩) < s) :
    OS.S (i.n + i.m) (ZeroDiagonalSchwartz.ofClassical
        (axisPairTwoBlockTimeSpatialSource i.n i.m
          η₁ (leftSpatialHermiteBlock d i r)
          η₂ (rightSpatialHermiteBlock d i r) t)) =
      generatorSplitAbsoluteSpatialSchwingerCLM
        OS i η₁ hη₁ η₂ hη₂ s t ht.le hspan
        (spatialHermite d (k + 1) (Nat.succ_pos k) r) := by
  have hschwinger :=
    axisPairTwoBlockTimeSpatialSource_schwinger_eq_global
      OS i.n i.m η₁ hη₁ (leftSpatialHermiteBlock d i r)
        η₂ hη₂ (rightSpatialHermiteBlock d i r) s t ht
  have hsource :
      axisPairGlobalTimeSpatialSource i.n i.m s t
          (axisPairBlockTimeSpatialTensor i.n i.m
            η₁ (leftSpatialHermiteBlock d i r)
            η₂ (rightSpatialHermiteBlock d i r)) =
        axisPairGlobalAbsoluteSpatialSourceCLM i.n i.m
          η₁ η₂ s t (generatorSplitSpatialHermite i r) := by
    rw [axisPairGlobalAbsoluteSpatialSourceCLM_apply,
      axisPairSeparateTimeSpatialTensor_generatorHermite]
  let Z :=
    axisPairGlobalAbsoluteSpatialSourceZeroCLM
      (d := d) i.n i.m i.hn i.hm η₁ hη₁ η₂ hη₂ s t ht.le hspan
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (axisPairGlobalTimeSpatialSource i.n i.m s t
          (axisPairBlockTimeSpatialTensor i.n i.m
            η₁ (leftSpatialHermiteBlock d i r)
            η₂ (rightSpatialHermiteBlock d i r))) := by
    rw [hsource]
    exact (Z (generatorSplitSpatialHermite i r)).2
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
          (axisPairGlobalTimeSpatialSource i.n i.m s t
            (axisPairBlockTimeSpatialTensor i.n i.m
              η₁ (leftSpatialHermiteBlock d i r)
              η₂ (rightSpatialHermiteBlock d i r))) =
        Z (generatorSplitSpatialHermite i r) := by
    apply Subtype.ext
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hvanish]
    exact hsource
  rw [hschwinger, hzero]
  rfl

end OSIIChapterV
end OSReconstruction
