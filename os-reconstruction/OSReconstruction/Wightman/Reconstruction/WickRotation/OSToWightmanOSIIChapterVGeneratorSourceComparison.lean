/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialFields
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison

















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- The unreflected tensor in separate left/right Section 4.3 difference
coordinates. Complex conjugation is applied to the complete left block. -/
noncomputable def axisPairBlockTimeSpatialTensor
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    SchwartzNPoint d (n + m) :=
  (section43NPointTimeSpatialTensor d n η₁ χ₁).conj.tensorProduct
    (section43NPointTimeSpatialTensor d m η₂ χ₂)

/-- Absolute spatial coordinates of a generator block point, reindexed from
the split cardinality `i.n + i.m` to the common cardinality `k + 1`. -/
def generatorAbsoluteSpatialCoordinates
    {k : ℕ} (i : GeneratorIndex k)
    (q : NPointDomain d (i.n + i.m)) :
    Fin (k + 1) → Fin d → ℝ :=
  fun c j =>
    section43SpatialParticleCLE d (i.n + i.m)
      (section43QSpatial (d := d) (n := i.n + i.m) q)
      (Fin.cast i.absoluteCard_eq c) j

/-- On a generator Hermite block, the separate-coordinate tensor factors
into the two finite-dimensional time profiles and the common absolute
spatial Hermite basis vector. Thus every residual split dependence is
carried by the time factor, not by the spatial basis. -/
theorem axisPairBlockTimeSpatialTensor_generatorHermite_apply
    {k : ℕ} (i : GeneratorIndex k) (r : ℕ)
    (η₁ : SchwartzMap (Fin i.n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin i.m → ℝ) ℂ)
    (q : NPointDomain d (i.n + i.m)) :
    axisPairBlockTimeSpatialTensor i.n i.m
        η₁ (leftSpatialHermiteBlock d i r)
        η₂ (rightSpatialHermiteBlock d i r) q =
      starRingEnd ℂ
          (η₁ (section43QTime (d := d) (n := i.n)
            (section43LeftBlock d i.n i.m q))) *
        η₂ (section43QTime (d := d) (n := i.m)
          (section43RightTailBlock d i.n i.m q)) *
        spatialHermite d (k + 1) (Nat.succ_pos k) r
          ((section43SpatialParticleCLE d (k + 1)).symm
            (generatorAbsoluteSpatialCoordinates i q)) := by
  rw [axisPairBlockTimeSpatialTensor,
    SchwartzMap.tensorProduct_apply, SchwartzMap.conj_apply,
    section43NPointTimeSpatialTensor_apply,
    section43NPointTimeSpatialTensor_apply]
  rw [map_mul]
  have hleft :
      starRingEnd ℂ
          (leftSpatialHermiteBlock d i r
            (section43QSpatial (d := d) (n := i.n)
              (splitFirst i.n i.m q))) =
        leftSpatialHermiteBlock d i r
          (section43QSpatial (d := d) (n := i.n)
            (splitFirst i.n i.m q)) := by
    simp [leftSpatialHermiteBlock_apply, spatialHermiteFactor]
  have hspatial :
      spatialHermite d (k + 1) (Nat.succ_pos k) r
          ((section43SpatialParticleCLE d (k + 1)).symm
            (generatorAbsoluteSpatialCoordinates i q)) =
        leftSpatialHermiteBlock d i r
            (section43QSpatial (d := d) (n := i.n)
              (splitFirst i.n i.m q)) *
          rightSpatialHermiteBlock d i r
            (section43QSpatial (d := d) (n := i.m)
              (splitLast i.n i.m q)) := by
    have hleftPoint :
        (section43SpatialParticleCLE d i.n).symm
            (fun a =>
              generatorAbsoluteSpatialCoordinates i q
                (i.leftAbsoluteIndex a)) =
          section43QSpatial (d := d) (n := i.n)
            (splitFirst i.n i.m q) := by
      apply (section43SpatialParticleCLE d i.n).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      funext a j
      simpa [generatorAbsoluteSpatialCoordinates,
        GeneratorIndex.leftAbsoluteIndex] using
        (section43QSpatial_leftBlock_apply
          d i.n i.m q (a, j)).symm
    have hrightPoint :
        (section43SpatialParticleCLE d i.m).symm
            (fun b =>
              generatorAbsoluteSpatialCoordinates i q
                (i.rightAbsoluteIndex b)) =
          section43QSpatial (d := d) (n := i.m)
            (splitLast i.n i.m q) := by
      apply (section43SpatialParticleCLE d i.m).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      funext b j
      simpa [generatorAbsoluteSpatialCoordinates,
        GeneratorIndex.rightAbsoluteIndex] using
        (section43QSpatial_rightTailBlock_apply
          d i.n i.m q (b, j)).symm
    rw [spatialHermite_eq_leftBlock_mul_rightBlock]
    rw [hleftPoint, hrightPoint]
  rw [hleft, hspatial]
  ac_rfl

/-- The reflected-left and shifted-right source occurring on the positive
real edge of a Chapter V generator mode. -/
noncomputable def axisPairTwoBlockTimeSpatialSource
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (t : ℝ) :
    SchwartzNPoint d (n + m) :=
  (section43OrderedPullbackTimeSpatialTensorCLM d n χ₁ η₁
      ).osConjTensorProduct
    (timeShiftSchwartzNPoint (d := d) t
      (section43OrderedPullbackTimeSpatialTensorCLM d m χ₂ η₂))

/-- Restore chronological point order in the reflected left block. -/
noncomputable def axisPairPermutedTwoBlockTimeSpatialSource
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (t : ℝ) :
    SchwartzNPoint d (n + m) :=
  reindexSchwartz (d := d) (osiiAxisPairLeftBlockReversePerm n m)
    (axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t)

/-- On the block-global absolute chart, the chronologically reordered raw
source is exactly the separate-coordinate time/spatial tensor. -/
theorem axisPairPermutedTwoBlockTimeSpatialSource_rawConfig
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (t : ℝ)
    (q : NPointDomain d (n + m)) :
    axisPairPermutedTwoBlockTimeSpatialSource
        n m η₁ χ₁ η₂ χ₂ t
        (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m 0 t q) =
      axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂ q := by
  let xL : NPointDomain d n :=
    (section43DiffCoordRealCLE d n).symm (splitFirst n m q)
  let xR : NPointDomain d m :=
    (section43DiffCoordRealCLE d m).symm (splitLast n m q)
  have hleft :
      timeReflectionN d
        (splitFirst n m
          (fun k =>
            osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
              d n m 0 t q
              (osiiAxisPairLeftBlockReversePerm n m k))) = xL := by
    ext i μ
    change timeReflection d
        (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
          d n m 0 t q
          (osiiAxisPairLeftBlockReversePerm n m
            (Fin.castAdd m i))) μ =
      xL i μ
    rw [osiiAxisPairLeftBlockReversePerm_castAdd,
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_left]
    simp only [Fin.rev_rev]
    change
      timeReflection d
          (timeReflection d (xL i) + timeShiftVec d 0) μ =
        xL i μ
    have hzero : timeShiftVec d 0 = 0 := by
      ext ν
      simp [timeShiftVec]
    rw [hzero, add_zero, timeReflection_timeReflection]
  have hright :
      (fun j =>
        splitLast n m
            (fun k =>
              osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
                d n m 0 t q
                (osiiAxisPairLeftBlockReversePerm n m k)) j -
          timeShiftVec d t) = xR := by
    ext j μ
    change
      (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig
          d n m 0 t q
          (osiiAxisPairLeftBlockReversePerm n m
            (Fin.natAdd n j)) -
        timeShiftVec d t) μ =
      xR j μ
    rw [osiiAxisPairLeftBlockReversePerm_natAdd,
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_right]
    simp [xR]
  rw [show
      axisPairPermutedTwoBlockTimeSpatialSource
          n m η₁ χ₁ η₂ χ₂ t
          (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m 0 t q) =
        starRingEnd ℂ
            (section43OrderedPullbackTimeSpatialTensorCLM d n χ₁ η₁ xL) *
          section43OrderedPullbackTimeSpatialTensorCLM d m χ₂ η₂ xR by
        simp only [axisPairPermutedTwoBlockTimeSpatialSource,
          axisPairTwoBlockTimeSpatialSource, reindexSchwartz_apply,
          SchwartzNPoint.osConjTensorProduct,
          SchwartzMap.tensorProduct_apply, SchwartzNPoint.osConj_apply,
          timeShiftSchwartzNPoint_apply]
        rw [hleft, hright]]
  simp [axisPairBlockTimeSpatialTensor,
    section43OrderedPullbackTimeSpatialTensorCLM_apply,
    section43NPointTimeSpatialTensor_apply, xL, xR]

/-- Pull an arbitrary separate-coordinate block test through the affine
two-block-to-global spacetime chart and then back to absolute coordinates. -/
noncomputable def axisPairGlobalTimeSpatialSource
    (n m : ℕ) (s t : ℝ)
    (F : SchwartzNPoint d (n + m)) :
    SchwartzNPoint d (n + m) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d (n + m))
    (osiiAxisPairBlockGlobalSpacetimePullbackCLM d n m s t F)

omit [NeZero d] in
/-- The affine global source evaluates to its original block test on the
block-global absolute chart. -/
@[simp] theorem axisPairGlobalTimeSpatialSource_config
    (n m : ℕ) (s t : ℝ)
    (F : SchwartzNPoint d (n + m))
    (q : NPointDomain d (n + m)) :
    axisPairGlobalTimeSpatialSource n m s t F
        (osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q) =
      F q := by
  rw [axisPairGlobalTimeSpatialSource,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  simp only [Function.comp_apply]
  rw [section43DiffCoordRealCLE_blockGlobalAbsoluteSpacetimeConfig,
    osiiAxisPairBlockGlobalSpacetimePullbackCLM_affine]

/-- The affine global time/spatial source is the chronologically reordered
raw two-block source after removing the auxiliary common translation. -/
theorem axisPairGlobalTimeSpatialSource_eq_permuted_translate
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (s t : ℝ)
    (x : NPointDomain d (n + m)) :
    axisPairGlobalTimeSpatialSource n m s t
        (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂) x =
      axisPairPermutedTwoBlockTimeSpatialSource
        n m η₁ χ₁ η₂ χ₂ t
        (fun k => x k + (-timeShiftVec d s)) := by
  obtain ⟨q, hq⟩ :=
    osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_surjective
      (d := d) n m t (fun k => x k + (-timeShiftVec d s))
  have hshift :
      osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q = x := by
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_commonShift, hq]
    ext k μ
    simp [timeShiftVec]
  have hback :
      (fun k =>
        osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m s t q k +
          (-timeShiftVec d s)) =
        osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig d n m 0 t q := by
    rw [osiiAxisPairBlockGlobalAbsoluteSpacetimeConfig_commonShift]
    ext k μ
    simp [timeShiftVec]
  rw [← hshift, axisPairGlobalTimeSpatialSource_config, hback]
  exact
    (axisPairPermutedTwoBlockTimeSpatialSource_rawConfig
      n m η₁ χ₁ η₂ χ₂ t q).symm

/-- E3 restores chronological order and E1 removes the auxiliary common
translation. Thus every reflected two-block Section 4.3 time/spatial source
has the Schwinger value of its affine global source. -/
theorem axisPairTwoBlockTimeSpatialSource_schwinger_eq_global
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (hη₁ : tsupport (η₁ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (hη₂ : tsupport (η₂ : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (s t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t)) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (axisPairGlobalTimeSpatialSource n m s t
          (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂))) := by
  let left :=
    section43OrderedPullbackTimeSpatialTensorCLM d n χ₁ η₁
  let right :=
    section43OrderedPullbackTimeSpatialTensorCLM d m χ₂ η₂
  have hleft :
      tsupport ((left : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n :=
    section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
      d n χ₁ η₁ hη₁
  have hright :
      tsupport ((right : SchwartzNPoint d m) :
          NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m :=
    section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
      d m χ₂ η₂ hη₂
  have hraw :
      VanishesToInfiniteOrderOnCoincidence
        (axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t) := by
    change VanishesToInfiniteOrderOnCoincidence
      (left.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t right))
    exact
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
        (d := d) left hleft right hright t ht
  have hpermuted :
      VanishesToInfiniteOrderOnCoincidence
        (axisPairPermutedTwoBlockTimeSpatialSource
          n m η₁ χ₁ η₂ χ₂ t) :=
    VanishesToInfiniteOrderOnCoincidence.compCLMOfContinuousLinearEquiv
      hraw (osiiAxisPairLeftBlockReversePerm n m)
  have hglobal_eq :
      axisPairGlobalTimeSpatialSource n m s t
          (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂) =
        translateSchwartzNPoint (d := d) (timeShiftVec d s)
          (axisPairPermutedTwoBlockTimeSpatialSource
            n m η₁ χ₁ η₂ χ₂ t) := by
    ext x
    rw [axisPairGlobalTimeSpatialSource_eq_permuted_translate]
    simp [translateSchwartzNPoint_apply, sub_eq_add_neg]
  have hglobal :
      VanishesToInfiniteOrderOnCoincidence
        (axisPairGlobalTimeSpatialSource n m s t
          (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂)) := by
    rw [hglobal_eq]
    exact
      (VanishesToInfiniteOrderOnCoincidence.translateSchwartzNPoint_iff
        (timeShiftVec d s)
        (axisPairPermutedTwoBlockTimeSpatialSource
          n m η₁ χ₁ η₂ χ₂ t)).2 hpermuted
  let rawZ : ZeroDiagonalSchwartz d (n + m) :=
    ⟨axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t, hraw⟩
  let permutedZ : ZeroDiagonalSchwartz d (n + m) :=
    ⟨axisPairPermutedTwoBlockTimeSpatialSource
      n m η₁ χ₁ η₂ χ₂ t, hpermuted⟩
  let globalZ : ZeroDiagonalSchwartz d (n + m) :=
    ⟨axisPairGlobalTimeSpatialSource n m s t
      (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂), hglobal⟩
  have hE3 : OS.S (n + m) rawZ = OS.S (n + m) permutedZ := by
    refine OS.E3_symmetric (n := n + m)
      (σ := osiiAxisPairLeftBlockReversePerm n m) rawZ permutedZ ?_
    intro x
    rfl
  have hE1 : OS.S (n + m) permutedZ = OS.S (n + m) globalZ := by
    refine OS.E1_translation_invariant (n + m) (-timeShiftVec d s)
      permutedZ globalZ ?_
    intro x
    exact axisPairGlobalTimeSpatialSource_eq_permuted_translate
      n m η₁ χ₁ η₂ χ₂ s t x
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := axisPairTwoBlockTimeSpatialSource n m η₁ χ₁ η₂ χ₂ t) hraw]
  rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
    (f := axisPairGlobalTimeSpatialSource n m s t
      (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂)) hglobal]
  exact hE3.trans hE1

end OSIIChapterV
end OSReconstruction
