import OSReconstruction.GeneralResults.FinProductIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceGeometry

/-!
# Volume preservation of the Chapter V block-global time chart

The two-block time chart is assembled from:

* splitting and appending finite coordinate blocks;
* the triangular successive-difference chart on each block;
* reversal and sign change of the reflected left block;
* the triangular global successive-difference chart.

Every constituent preserves Lebesgue measure. Consequently the full linear
chart and its affine translates have Jacobian of absolute value one. This is
the change-of-variables input needed to expose the two independent time
approximate identities in the Chapter V mixed moving-slice scalar.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Splitting off the head coordinate of a finite real tuple preserves
Lebesgue integration. -/
theorem integral_finCons_eq
    (k : ℕ)
    (F : (Fin (k + 1) → ℝ) → ℂ) :
    (∫ p : ℝ × (Fin k → ℝ), F (Fin.cons p.1 p.2)
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin k → ℝ)))) =
      ∫ y : Fin (k + 1) → ℝ, F y := by
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) => ℝ) 0
  have hmp :
      MeasurePreserving e
        (volume : Measure (Fin (k + 1) → ℝ))
        ((volume : Measure ℝ).prod
          (volume : Measure (Fin k → ℝ))) := by
    rw [← Measure.volume_eq_prod]
    simpa [e] using
      (MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0)
  have he :
      (fun p : ℝ × (Fin k → ℝ) => Fin.cons p.1 p.2) =
        fun p => e.symm p := by
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth_zero]
  simp_rw [congrFun he]
  exact hmp.symm.integral_comp' F

private def section43TimeAsOnePointME (n : ℕ) :
    (Fin n → ℝ) ≃ᵐ (Fin n → Fin 1 → ℝ) :=
  (section43TimeAsOnePointCLE n).toHomeomorph.toMeasurableEquiv

private theorem section43TimeAsOnePointME_measurePreserving (n : ℕ) :
    MeasurePreserving
      (section43TimeAsOnePointME n)
      (volume : Measure (Fin n → ℝ))
      (volume : Measure (Fin n → Fin 1 → ℝ)) := by
  have hcoord :
      ∀ _ : Fin n,
        MeasurePreserving
          (fun x : ℝ => fun _ : Fin 1 => x)
          (volume : Measure ℝ)
          (volume : Measure (Fin 1 → ℝ)) := by
    intro i
    have heq :
        (fun x : ℝ => fun _ : Fin 1 => x) =
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm := by
      funext x j
      simp
    rw [heq]
    exact (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  change MeasurePreserving (fun x i j => x i)
    (volume : Measure (Fin n → ℝ))
    (volume : Measure (Fin n → Fin 1 → ℝ))
  exact MeasureTheory.volume_preserving_pi hcoord

private def section43ScalarDiffME (n : ℕ) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (section43ScalarDiffCLE n).toHomeomorph.toMeasurableEquiv

/-- The scalar successive-difference chart preserves Lebesgue measure. -/
theorem section43ScalarDiffME_measurePreserving (n : ℕ) :
    MeasurePreserving
      (section43ScalarDiffME n)
      (volume : Measure (Fin n → ℝ))
      (volume : Measure (Fin n → ℝ)) := by
  let eTime := section43TimeAsOnePointME n
  let eDiff :=
    (BHW.realDiffCoordCLE n 0).toHomeomorph.toMeasurableEquiv
  have hTime := section43TimeAsOnePointME_measurePreserving n
  have hDiff :
      MeasurePreserving eDiff
        (volume : Measure (Fin n → Fin 1 → ℝ))
        (volume : Measure (Fin n → Fin 1 → ℝ)) := by
    have hDiffSymm :
        MeasurePreserving eDiff.symm
          (volume : Measure (Fin n → Fin 1 → ℝ))
          (volume : Measure (Fin n → Fin 1 → ℝ)) := by
      simpa [eDiff] using
        (BHW.realDiffCoordCLE_symm_measurePreserving n 0)
    simpa using MeasurePreserving.symm eDiff.symm hDiffSymm
  have hcomp := hTime.trans (hDiff.trans hTime.symm)
  convert hcomp using 1 <;> ext x i <;>
    simp [section43ScalarDiffME, section43ScalarDiffCLE,
      section43TimeAsOnePointME, eTime, eDiff,
      BHW.realDiffCoordCLE_apply]

/-- Appending two finite real coordinate blocks preserves Lebesgue measure. -/
private theorem finAppendCLE_measurePreserving (n m : ℕ) :
    MeasurePreserving
      (⇑(SCV.finAppendCLE n m))
      (volume : Measure ((Fin n → ℝ) × (Fin m → ℝ)))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  have h :=
    (MeasureTheory.volume_preserving_finAddProd n m ℝ).symm
  have heq :
      (⇑(SCV.finAppendCLE n m)) =
        (MeasurableEquiv.finAddProd n m ℝ).symm := by
    funext p
    rw [MeasurableEquiv.finAddProd_symm_apply]
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp
    · intro j
      simp
  rw [heq]
  exact h

/-- Splitting a finite real coordinate block into two blocks preserves
Lebesgue measure. -/
private theorem finAppendCLE_symm_measurePreserving (n m : ℕ) :
    MeasurePreserving
      (⇑(SCV.finAppendCLE n m).symm)
      (volume : Measure (Fin (n + m) → ℝ))
      (volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))) := by
  let e :=
    (SCV.finAppendCLE n m).toHomeomorph.toMeasurableEquiv
  have he :
      MeasurePreserving e
        (volume : Measure ((Fin n → ℝ) × (Fin m → ℝ)))
        (volume : Measure (Fin (n + m) → ℝ)) := by
    simpa [e] using finAppendCLE_measurePreserving n m
  simpa [e] using MeasurePreserving.symm e he

private def axisPairBlockwiseTimeDiffME (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃ᵐ (Fin (n + m) → ℝ) :=
  (osiiAxisPairBlockwiseTimeDiffCLE n m).toHomeomorph.toMeasurableEquiv

private theorem axisPairBlockwiseTimeDiffME_measurePreserving
    (n m : ℕ) :
    MeasurePreserving
      (axisPairBlockwiseTimeDiffME n m)
      (volume : Measure (Fin (n + m) → ℝ))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  have hSplit := finAppendCLE_symm_measurePreserving n m
  have hProd :
      MeasurePreserving
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          (section43ScalarDiffCLE n p.1, section43ScalarDiffCLE m p.2))
        (volume :
          Measure ((Fin n → ℝ) × (Fin m → ℝ)))
        (volume :
          Measure ((Fin n → ℝ) × (Fin m → ℝ))) := by
    exact MeasurePreserving.prod
      (section43ScalarDiffME_measurePreserving n)
      (section43ScalarDiffME_measurePreserving m)
  have hAppend := finAppendCLE_measurePreserving n m
  have hprodSplit :
      MeasurePreserving
        (fun x : Fin (n + m) → ℝ =>
          (section43ScalarDiffCLE n ((SCV.finAppendCLE n m).symm x).1,
            section43ScalarDiffCLE m ((SCV.finAppendCLE n m).symm x).2))
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))) :=
    hProd.comp hSplit
  have hcomp :
      MeasurePreserving
        (fun x : Fin (n + m) → ℝ =>
          SCV.finAppendCLE n m
            (section43ScalarDiffCLE n ((SCV.finAppendCLE n m).symm x).1,
              section43ScalarDiffCLE m ((SCV.finAppendCLE n m).symm x).2))
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure (Fin (n + m) → ℝ)) :=
    hAppend.comp hprodSplit
  convert hcomp using 1 <;> ext x i <;>
    simp [axisPairBlockwiseTimeDiffME,
      osiiAxisPairBlockwiseTimeDiffCLE, section43ScalarDiffME]

private def reflectReverseLeftTimeME (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃ᵐ (Fin (n + m) → ℝ) :=
  (osiiAxisPairReflectReverseLeftTimeCLE n m
    ).toHomeomorph.toMeasurableEquiv

private theorem reflectReverseLeftBlock_measurePreserving (n : ℕ) :
    MeasurePreserving
      (fun x : Fin n → ℝ => fun i => -x (Fin.rev i))
      (volume : Measure (Fin n → ℝ))
      (volume : Measure (Fin n → ℝ)) := by
  have hrev :
      MeasurePreserving
        (fun x : Fin n → ℝ => fun i => x (Fin.rev i))
        (volume : Measure (Fin n → ℝ))
        (volume : Measure (Fin n → ℝ)) := by
    let e : Fin n ≃ Fin n := Fin.revPerm
    have heq :
        (MeasurableEquiv.piCongrLeft
            (fun _ : Fin n => ℝ) e : (Fin n → ℝ) → (Fin n → ℝ)) =
          (fun x : Fin n → ℝ => fun i => x (Fin.rev i)) := by
      funext x
      let x' : (a : Fin n) → (fun _ : Fin n => ℝ) (e a) := x
      funext i
      simpa [e] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : Fin n => ℝ) e x' (Fin.rev i))
    rw [← heq]
    exact MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => ℝ) e
  have hneg :
      MeasurePreserving
        (fun x : Fin n → ℝ => fun i => -x i)
        (volume : Measure (Fin n → ℝ))
        (volume : Measure (Fin n → ℝ)) := by
    exact MeasureTheory.volume_preserving_pi fun _ =>
      MeasureTheory.Measure.measurePreserving_neg
        (volume : Measure ℝ)
  simpa [Function.comp_def] using hneg.comp hrev

private theorem reflectReverseLeftTimeME_measurePreserving
    (n m : ℕ) :
    MeasurePreserving
      (reflectReverseLeftTimeME n m)
      (volume : Measure (Fin (n + m) → ℝ))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  have hSplit := finAppendCLE_symm_measurePreserving n m
  have hLeft :
      MeasurePreserving
        (fun x : Fin n → ℝ => fun i => -x (Fin.rev i))
        (volume : Measure (Fin n → ℝ))
        (volume : Measure (Fin n → ℝ)) := by
    exact reflectReverseLeftBlock_measurePreserving n
  have hProd :
      MeasurePreserving
        (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          ((fun i => -p.1 (Fin.rev i)), p.2))
        (volume :
          Measure ((Fin n → ℝ) × (Fin m → ℝ)))
        (volume :
          Measure ((Fin n → ℝ) × (Fin m → ℝ))) := by
    exact MeasurePreserving.prod hLeft
      (MeasurePreserving.id (volume : Measure (Fin m → ℝ)))
  have hAppend := finAppendCLE_measurePreserving n m
  have hprodSplit :
      MeasurePreserving
        (fun x : Fin (n + m) → ℝ =>
          ((fun i => -((SCV.finAppendCLE n m).symm x).1 (Fin.rev i)),
            ((SCV.finAppendCLE n m).symm x).2))
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))) :=
    hProd.comp hSplit
  have hcomp :
      MeasurePreserving
        (fun x : Fin (n + m) → ℝ =>
          SCV.finAppendCLE n m
            ((fun i => -((SCV.finAppendCLE n m).symm x).1 (Fin.rev i)),
              ((SCV.finAppendCLE n m).symm x).2))
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure (Fin (n + m) → ℝ)) :=
    hAppend.comp hprodSplit
  have heq :
      (reflectReverseLeftTimeME n m :
        (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) =
        fun x =>
          SCV.finAppendCLE n m
            ((fun i => -((SCV.finAppendCLE n m).symm x).1 (Fin.rev i)),
              ((SCV.finAppendCLE n m).symm x).2) := by
    funext x
    apply congrArg (SCV.finAppendCLE n m)
    congr 1
  rw [heq]
  exact hcomp

private def axisPairBlockGlobalTimeME (n m : ℕ) :
    (Fin (n + m) → ℝ) ≃ᵐ (Fin (n + m) → ℝ) :=
  (osiiAxisPairBlockGlobalTimeCLE n m
    ).toHomeomorph.toMeasurableEquiv

/-- The linear two-block-to-global time chart preserves Lebesgue measure. -/
theorem axisPairBlockGlobalTimeME_measurePreserving
    (n m : ℕ) :
    MeasurePreserving
      (axisPairBlockGlobalTimeME n m)
      (volume : Measure (Fin (n + m) → ℝ))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  have hBlock :=
    (axisPairBlockwiseTimeDiffME_measurePreserving n m).symm
  have hReflect :=
    reflectReverseLeftTimeME_measurePreserving n m
  have hGlobal :=
    section43ScalarDiffME_measurePreserving (n + m)
  have hcomp := hBlock.trans (hReflect.trans hGlobal)
  convert hcomp using 1 <;> ext x i <;>
    simp [axisPairBlockGlobalTimeME,
      osiiAxisPairBlockGlobalTimeCLE,
      axisPairBlockwiseTimeDiffME,
      reflectReverseLeftTimeME,
      section43ScalarDiffME]

/-- Every affine block-global time chart has the same unit Jacobian as its
linear part. -/
theorem axisPairBlockGlobalTimeAffine_measurePreserving
    (n m : ℕ) (s t : ℝ) :
    MeasurePreserving
      (osiiAxisPairBlockGlobalTimeAffine n m s t)
      (volume : Measure (Fin (n + m) → ℝ))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  have hlinear :
      MeasurePreserving
        (⇑(osiiAxisPairBlockGlobalTimeCLE n m))
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure (Fin (n + m) → ℝ)) := by
    simpa [axisPairBlockGlobalTimeME] using
      axisPairBlockGlobalTimeME_measurePreserving n m
  have htranslate :=
    MeasureTheory.measurePreserving_add_right
      (volume : Measure (Fin (n + m) → ℝ))
      (osiiAxisPairGlobalTimeDiffShift n m s t)
  change MeasurePreserving
    (fun x => osiiAxisPairBlockGlobalTimeCLE n m x +
      osiiAxisPairGlobalTimeDiffShift n m s t)
    (volume : Measure (Fin (n + m) → ℝ))
    (volume : Measure (Fin (n + m) → ℝ))
  exact htranslate.comp hlinear

/-- Integral change of variables through the affine block-global time chart. -/
theorem integral_comp_axisPairBlockGlobalTimeAffine
    (n m : ℕ) (s t : ℝ)
    (F : (Fin (n + m) → ℝ) → ℂ) :
    (∫ δ : Fin (n + m) → ℝ,
        F (osiiAxisPairBlockGlobalTimeAffine n m s t δ)) =
      ∫ y : Fin (n + m) → ℝ, F y := by
  let eLinear :=
    (osiiAxisPairBlockGlobalTimeCLE n m).toHomeomorph.toMeasurableEquiv
  let eAffine :=
    eLinear.trans
      (MeasurableEquiv.addRight
        (osiiAxisPairGlobalTimeDiffShift n m s t))
  have hAffine :
      MeasurePreserving eAffine
        (volume : Measure (Fin (n + m) → ℝ))
        (volume : Measure (Fin (n + m) → ℝ)) := by
    convert axisPairBlockGlobalTimeAffine_measurePreserving n m s t using 1 <;>
      ext x i <;> rfl
  simpa [eAffine, eLinear, osiiAxisPairBlockGlobalTimeAffine] using
    hAffine.integral_comp' F

/-- The block-global cutoff becomes the product of its independent left and
right tests after the affine time-coordinate change. -/
theorem integral_osiiAxisPairGlobalTimeCutoff_mul
    (n m : ℕ)
    (η₁ : SchwartzMap (Fin n → ℝ) ℂ)
    (η₂ : SchwartzMap (Fin m → ℝ) ℂ)
    (s t : ℝ)
    (H : (Fin (n + m) → ℝ) → ℂ) :
    (∫ y : Fin (n + m) → ℝ,
        osiiAxisPairGlobalTimeCutoff n m η₁ η₂ s t y * H y) =
      ∫ δ : Fin (n + m) → ℝ,
        (η₁ (splitFirst n m δ) *
            η₂ (splitLast n m δ)) *
          H (osiiAxisPairBlockGlobalTimeAffine n m s t δ) := by
  rw [← integral_comp_axisPairBlockGlobalTimeAffine n m s t]
  apply integral_congr_ae
  filter_upwards with δ
  rw [osiiAxisPairGlobalTimeCutoff_affine]

end OSIIChapterV
end OSReconstruction
