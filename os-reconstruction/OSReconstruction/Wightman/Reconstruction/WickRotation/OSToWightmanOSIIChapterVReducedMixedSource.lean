import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGlobalProfile
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTimeSpatialTensor

/-!
# OS-II Chapter V reduced mixed time/spatial sources

The reflected mixed source starts from independent left and right
time/spatial tensors.  This file combines their spatial factors into one
full-arity Schwartz test.  The existing block-global normal form can then
transport the source to a single ordered time/spatial tensor, where the
basepoint reduction theorem applies.
-/

noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d n m : ℕ} [NeZero d]

/-- Split a full Section 4.3 spatial tuple into its left and right particle
blocks. -/
noncomputable def section43TwoBlockSpatialSplitCLE
    (d n m : ℕ) :
    Section43SpatialSpace d (n + m) ≃L[ℝ]
      Section43SpatialSpace d n × Section43SpatialSpace d m :=
  (section43SpatialParticleCLE d (n + m)).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin (n + m) => Fin d → ℝ)
      (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))).symm.trans
        ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ
          (Fin n) (Fin m) (fun _ => Fin d → ℝ)).trans
            ((section43SpatialParticleCLE d n).symm.prodCongr
              (section43SpatialParticleCLE d m).symm)))

@[simp]
theorem section43TwoBlockSpatialSplitCLE_fst_apply
    (η : Section43SpatialSpace d (n + m))
    (i : Fin n) (j : Fin d) :
    section43SpatialParticleCLE d n
        (section43TwoBlockSpatialSplitCLE d n m η).1 i j =
      section43SpatialParticleCLE d (n + m) η
        (Fin.castAdd m i) j := by
  rfl

@[simp]
theorem section43TwoBlockSpatialSplitCLE_snd_apply
    (η : Section43SpatialSpace d (n + m))
    (i : Fin m) (j : Fin d) :
    section43SpatialParticleCLE d m
        (section43TwoBlockSpatialSplitCLE d n m η).2 i j =
      section43SpatialParticleCLE d (n + m) η
        (Fin.natAdd n i) j := by
  rfl

/-- The full spatial Schwartz test obtained by multiplying the conjugated
left block with the right block. -/
noncomputable def section43TwoBlockSpatialProduct
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    SchwartzMap (Section43SpatialSpace d (n + m)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43TwoBlockSpatialSplitCLE d n m)
    (SCV.schwartzExternalProduct χ₁.conj χ₂)

@[simp]
theorem section43TwoBlockSpatialProduct_apply
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : Section43SpatialSpace d (n + m)) :
    section43TwoBlockSpatialProduct χ₁ χ₂ η =
      starRingEnd ℂ
          (χ₁ (section43TwoBlockSpatialSplitCLE d n m η).1) *
        χ₂ (section43TwoBlockSpatialSplitCLE d n m η).2 := by
  rw [section43TwoBlockSpatialProduct,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change
    SCV.schwartzExternalProduct χ₁.conj χ₂
        (section43TwoBlockSpatialSplitCLE d n m η) =
      _
  rw [SCV.schwartzExternalProduct_apply, SchwartzMap.conj_apply]

theorem section43TwoBlockSpatialSplitCLE_qSpatial
    (q : NPointDomain d (n + m)) :
    section43TwoBlockSpatialSplitCLE d n m
        (section43QSpatial (d := d) (n := n + m) q) =
      (section43QSpatial (d := d) (n := n)
          (section43LeftBlock d n m q),
        section43QSpatial (d := d) (n := m)
          (section43RightTailBlock d n m q)) := by
  apply Prod.ext
  · apply (section43SpatialParticleCLE d n).injective
    funext i j
    rw [section43TwoBlockSpatialSplitCLE_fst_apply]
    exact (section43QSpatial_leftBlock_apply d n m q (i, j)).symm
  · apply (section43SpatialParticleCLE d m).injective
    funext i j
    rw [section43TwoBlockSpatialSplitCLE_snd_apply]
    exact (section43QSpatial_rightTailBlock_apply d n m q (i, j)).symm

/-- An arbitrary left/right time-spatial tensor is one full-arity separate
time tensor against the combined spatial product test. -/
theorem axisPairSeparateTimeSpatialTensor_twoBlockSpatialProduct
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    axisPairSeparateTimeSpatialTensor n m η₁ η₂
        (section43TwoBlockSpatialProduct χ₁ χ₂) =
      axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂ := by
  ext q
  rw [axisPairBlockTimeSpatialTensor,
    SchwartzMap.tensorProduct_apply, SchwartzMap.conj_apply,
    section43NPointTimeSpatialTensor_apply,
    section43NPointTimeSpatialTensor_apply]
  simp only [axisPairSeparateTimeSpatialTensor,
    section43NPointTimeSpatialTensor_apply]
  rw [section43TwoBlockSpatialProduct_apply,
    section43TwoBlockSpatialSplitCLE_qSpatial]
  have htime :
      section43QTime (d := d) (n := n + m) q =
        Fin.append
          (section43QTime (d := d) (n := n)
            (section43LeftBlock d n m q))
          (section43QTime (d := d) (n := m)
            (section43RightTailBlock d n m q)) := by
    ext c
    refine Fin.addCases ?_ ?_ c
    · intro i
      rw [Fin.append_left]
      exact (section43QTime_leftBlock d n m q i).symm
    · intro i
      rw [Fin.append_right]
      exact (section43QTime_rightTailBlock d n m q i).symm
  rw [htime, SCV.twoBlockProductSchwartz_apply]
  simp only [SchwartzMap.conj_apply, map_mul]
  ac_rfl

/-- The affine global source of arbitrary left/right spatial factors has the
single ordered time/spatial normal form used by basepoint reduction. -/
theorem axisPairGlobalTimeSpatialSource_twoBlock_normalForm
    (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (s t : ℝ) :
    axisPairGlobalTimeSpatialSource n m s t
        (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂) =
      section43OrderedPullbackTimeSpatialTensorCLM d (n + m)
        (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
          (d := d) n m
          (section43TwoBlockSpatialProduct χ₁ χ₂))
        (osiiAxisPairGlobalTimeCutoff n m η₁.conj η₂ s t) := by
  calc
    axisPairGlobalTimeSpatialSource n m s t
        (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂) =
      axisPairGlobalTimeSpatialSource n m s t
        (axisPairSeparateTimeSpatialTensor n m η₁ η₂
          (section43TwoBlockSpatialProduct χ₁ χ₂)) := by
            rw [axisPairSeparateTimeSpatialTensor_twoBlockSpatialProduct]
    _ =
      axisPairGlobalAbsoluteSpatialSourceCLM
        n m η₁ η₂ s t
          (section43TwoBlockSpatialProduct χ₁ χ₂) := rfl
    _ = _ := by
      have hnormal :=
        congrArg
          (fun L :
              SchwartzMap (Section43SpatialSpace d (n + m)) ℂ →L[ℂ]
                SchwartzNPoint d (n + m) =>
            L (section43TwoBlockSpatialProduct χ₁ χ₂))
          (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalAbsoluteSpatialSourceCLM_normalForm
            (d := d) n m hn hm η₁ η₂ s t)
      simpa using hnormal

/-- With no auxiliary right shift or common translation, the block-global
source is exactly the chronologically reordered reflected product source. -/
theorem axisPairGlobalTimeSpatialSource_zero_zero
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    axisPairGlobalTimeSpatialSource n m 0 0
        (axisPairBlockTimeSpatialTensor n m η₁ χ₁ η₂ χ₂) =
      axisPairPermutedTwoBlockTimeSpatialSource
        n m η₁ χ₁ η₂ χ₂ 0 := by
  ext x
  rw [axisPairGlobalTimeSpatialSource_eq_permuted_translate]
  congr 1
  funext k μ
  simp [timeShiftVec]

/-- The zero-shift chronological reflected product is one ordered full time
test against one transported full spatial test. -/
theorem axisPairPermutedTwoBlockTimeSpatialSource_zero_normalForm
    (hn : 0 < n) (hm : 0 < m)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d m) ℂ) :
    axisPairPermutedTwoBlockTimeSpatialSource
        n m η₁ χ₁ η₂ χ₂ 0 =
      section43OrderedPullbackTimeSpatialTensorCLM d (n + m)
        (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
          (d := d) n m
          (section43TwoBlockSpatialProduct χ₁ χ₂))
        (osiiAxisPairGlobalTimeCutoff n m η₁.conj η₂ 0 0) := by
  rw [← axisPairGlobalTimeSpatialSource_zero_zero]
  exact
    axisPairGlobalTimeSpatialSource_twoBlock_normalForm
      hn hm η₁ χ₁ η₂ χ₂ 0 0

/-- The mixed reflected source used by the Chapter V continuation is the
equal-arity reindexing of the concrete zero-shift two-block source. -/
theorem mixedReflectedChronologicalSource_timeSpatial_eq_reindex
    {k : ℕ}
    (η₁ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (η₂ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    mixedReflectedChronologicalSource
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ₁ η₁)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ₂ η₂) =
      reindexSchwartz (d := d) (finCongr (by omega))
        (axisPairPermutedTwoBlockTimeSpatialSource
          (k + 1) (k + 1) η₁ χ₁ η₂ χ₂ 0) := by
  have hzero :
      timeShiftSchwartzNPoint (d := d) 0
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (k + 1) χ₂ η₂) =
        section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ₂ η₂ := by
    ext x
    rw [timeShiftSchwartzNPoint_apply]
    congr 1
    funext i μ
    simp [timeShiftVec]
  unfold mixedReflectedChronologicalSource
  unfold axisPairPermutedTwoBlockTimeSpatialSource
  unfold axisPairTwoBlockTimeSpatialSource
  rw [hzero]
  ext x
  simp [reindexSchwartz_apply]

/-- Cast-free ordered time/spatial normal form of the mixed reflected source
at the exact Chapter V continuation arity. -/
theorem mixedReflectedChronologicalSource_timeSpatial_normalForm
    {k : ℕ}
    (η₁ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₁ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (η₂ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    mixedReflectedChronologicalSource
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ₁ η₁)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ₂ η₂) =
      section43OrderedPullbackTimeSpatialTensorCLM
        d ((k + (k + 1)) + 1)
        (section43SpatialSchwartzTransport d (by omega)
          (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
            (d := d) (k + 1) (k + 1)
            (section43TwoBlockSpatialProduct χ₁ χ₂)))
        (section43TimeSchwartzTransport (by omega)
          (osiiAxisPairGlobalTimeCutoff
            (k + 1) (k + 1) η₁.conj η₂ 0 0)) := by
  rw [mixedReflectedChronologicalSource_timeSpatial_eq_reindex]
  rw [axisPairPermutedTwoBlockTimeSpatialSource_zero_normalForm
    (d := d) (by omega) (by omega)]
  exact
    reindexSchwartz_orderedPullback_timeSpatialTensor
      (d := d) (by omega)
      (osiiAxisPairGlobalTimeCutoff
        (k + 1) (k + 1) η₁.conj η₂ 0 0)
      (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
        (d := d) (k + 1) (k + 1)
        (section43TwoBlockSpatialProduct χ₁ χ₂))

end OSIIChapterV
end OSReconstruction
