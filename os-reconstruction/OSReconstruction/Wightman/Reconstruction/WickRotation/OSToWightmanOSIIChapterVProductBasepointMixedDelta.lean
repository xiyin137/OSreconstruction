import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedMovingSlice

/-!
# Product-basepoint mixed delta representation

The full reflected mixed source has one fixed compact head time in each block
and one shrinking internal-gap source in each tail. This module regroups the
full time integral into the two head coordinates and the two internal blocks,
proves that regrouping preserves Lebesgue measure, and integrates out the
fixed heads.

The resulting exact identity is the source-facing input for the partial
two-index delta limit. No factorization of the continuation bridge coordinate
is used.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Regroup two head/tail pairs into one head pair and one tail pair. -/
private def pairHeadsTailsMeasurableEquiv (k : ℕ) :
    ((ℝ × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ))) ≃ᵐ
      ((ℝ × ℝ) × ((Fin k → ℝ) × (Fin k → ℝ))) :=
  (MeasurableEquiv.prodAssoc
      (α := ℝ) (β := Fin k → ℝ)
      (γ := ℝ × (Fin k → ℝ))).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.prodAssoc
          (α := Fin k → ℝ) (β := ℝ)
          (γ := Fin k → ℝ)).symm.trans
        ((MeasurableEquiv.prodCongr
            (MeasurableEquiv.prodComm :
              (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ))
            (MeasurableEquiv.refl (Fin k → ℝ))).trans
          (MeasurableEquiv.prodAssoc
            (α := ℝ) (β := Fin k → ℝ)
            (γ := Fin k → ℝ))))).trans
      (MeasurableEquiv.prodAssoc
        (α := ℝ) (β := ℝ)
        (γ := (Fin k → ℝ) × (Fin k → ℝ))).symm)

@[simp] private theorem pairHeadsTailsMeasurableEquiv_symm_apply
    (k : ℕ) (heads : ℝ × ℝ)
    (left right : Fin k → ℝ) :
    (pairHeadsTailsMeasurableEquiv k).symm
        (heads, (left, right)) =
      ((heads.1, left), (heads.2, right)) :=
  rfl

@[simp] private theorem splitTwoHeadsMeasurableEquiv_symm_apply
    (k : ℕ) (heads : ℝ × ℝ)
    (left right : Fin k → ℝ) :
    (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (k + 1) => ℝ) 0)
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (k + 1) => ℝ) 0)).symm
        ((heads.1, left), (heads.2, right)) =
      (Fin.cons heads.1 left, Fin.cons heads.2 right) :=
  by
    apply Prod.ext
    · change
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (k + 1) => ℝ) 0).symm
            (heads.1, left) =
          Fin.cons heads.1 left
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero,
        Fin.zero_succAbove, cast_eq]
      rfl
    · change
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (k + 1) => ℝ) 0).symm
            (heads.2, right) =
          Fin.cons heads.2 right
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero,
        Fin.zero_succAbove, cast_eq]
      rfl

/-- Split both full blocks into heads and tails, then append the two tails. -/
private def osiiMixedHeadTailMeasurableEquiv (k : ℕ) :
    (Fin ((k + 1) + (k + 1)) → ℝ) ≃ᵐ
      ((ℝ × ℝ) × (Fin (k + k) → ℝ)) :=
  (MeasurableEquiv.finAddProd (k + 1) (k + 1) ℝ).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0)
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0)).trans
      ((pairHeadsTailsMeasurableEquiv k).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (ℝ × ℝ))
          (MeasurableEquiv.finAddProd k k ℝ).symm)))

@[simp] private theorem finAddProd_apply_eq_split
    (k : ℕ) (tails : Fin (k + k) → ℝ) :
    MeasurableEquiv.finAddProd k k ℝ tails =
      (splitFirst k k tails, splitLast k k tails) := by
  apply (MeasurableEquiv.finAddProd k k ℝ).symm.injective
  rw [MeasurableEquiv.symm_apply_apply,
    MeasurableEquiv.finAddProd_symm_apply]
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp [splitFirst]
  · intro b
    rw [Fin.append_right]
    rfl

private theorem osiiMixedHeadTailMeasurableEquiv_symm_apply
    (k : ℕ)
    (heads : ℝ × ℝ)
    (tails : Fin (k + k) → ℝ) :
    (osiiMixedHeadTailMeasurableEquiv k).symm (heads, tails) =
      osiiMixedHeadTailDelta heads tails := by
  change
    (MeasurableEquiv.finAddProd (k + 1) (k + 1) ℝ).symm
        (((MeasurableEquiv.prodCongr
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (k + 1) => ℝ) 0)
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (k + 1) => ℝ) 0)).symm
          ((pairHeadsTailsMeasurableEquiv k).symm
            (heads, MeasurableEquiv.finAddProd k k ℝ tails)))) =
      osiiMixedHeadTailDelta heads tails
  rw [finAddProd_apply_eq_split]
  rw [pairHeadsTailsMeasurableEquiv_symm_apply,
    splitTwoHeadsMeasurableEquiv_symm_apply]
  change
    (MeasurableEquiv.finAddProd (k + 1) (k + 1) ℝ).symm
        (Fin.cons heads.1 (splitFirst k k tails),
          Fin.cons heads.2 (splitLast k k tails)) =
      osiiMixedHeadTailDelta heads tails
  rw [MeasurableEquiv.finAddProd_symm_apply]
  rfl

private theorem pairHeadsTailsMeasurableEquiv_measurePreserving
    (k : ℕ) :
    MeasurePreserving
      (pairHeadsTailsMeasurableEquiv k)
      (volume :
        Measure ((ℝ × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ))))
      (volume :
        Measure ((ℝ × ℝ) × ((Fin k → ℝ) × (Fin k → ℝ)))) := by
  have hAssoc₁ :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ)) ≃ᵐ
            ℝ × ((Fin k → ℝ) × (ℝ × (Fin k → ℝ))))
        (volume :
          Measure ((ℝ × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ))))
        (volume :
          Measure (ℝ × ((Fin k → ℝ) × (ℝ × (Fin k → ℝ))))) := by
    simpa using
      (measurePreserving_prodAssoc
        (volume : Measure ℝ)
        (volume : Measure (Fin k → ℝ))
        (volume : Measure (ℝ × (Fin k → ℝ))))
  have hAssoc₂ :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          ((Fin k → ℝ) × ℝ) × (Fin k → ℝ) ≃ᵐ
            (Fin k → ℝ) × (ℝ × (Fin k → ℝ))).symm
        (volume :
          Measure ((Fin k → ℝ) × (ℝ × (Fin k → ℝ))))
        (volume :
          Measure (((Fin k → ℝ) × ℝ) × (Fin k → ℝ))) := by
    simpa using
      (measurePreserving_prodAssoc
        (volume : Measure (Fin k → ℝ))
        (volume : Measure ℝ)
        (volume : Measure (Fin k → ℝ))).symm
  have hSwap :
      MeasurePreserving
        (MeasurableEquiv.prodComm :
          (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ))
        (volume : Measure ((Fin k → ℝ) × ℝ))
        (volume : Measure (ℝ × (Fin k → ℝ))) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure (Fin k → ℝ)))
        (ν := (volume : Measure ℝ)))
  have hSwapProd :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.prodComm :
            (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ))
          (MeasurableEquiv.refl (Fin k → ℝ)))
        (volume :
          Measure (((Fin k → ℝ) × ℝ) × (Fin k → ℝ)))
        (volume :
          Measure ((ℝ × (Fin k → ℝ)) × (Fin k → ℝ))) := by
    simpa using
      (MeasurePreserving.prod hSwap
        (MeasurePreserving.id (volume : Measure (Fin k → ℝ))))
  have hAssoc₃ :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × (Fin k → ℝ)) × (Fin k → ℝ) ≃ᵐ
            ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))
        (volume :
          Measure ((ℝ × (Fin k → ℝ)) × (Fin k → ℝ)))
        (volume :
          Measure (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))) := by
    simpa using
      (measurePreserving_prodAssoc
        (volume : Measure ℝ)
        (volume : Measure (Fin k → ℝ))
        (volume : Measure (Fin k → ℝ)))
  have hInner :
      MeasurePreserving
        ((MeasurableEquiv.prodAssoc
          (α := Fin k → ℝ) (β := ℝ)
          (γ := Fin k → ℝ)).symm.trans
            ((MeasurableEquiv.prodCongr
              (MeasurableEquiv.prodComm :
                (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ))
              (MeasurableEquiv.refl (Fin k → ℝ))).trans
                (MeasurableEquiv.prodAssoc
                  (α := ℝ) (β := Fin k → ℝ)
                  (γ := Fin k → ℝ))))
        (volume :
          Measure ((Fin k → ℝ) × (ℝ × (Fin k → ℝ))))
        (volume :
          Measure (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))) :=
    hAssoc₂.trans (hSwapProd.trans hAssoc₃)
  have hProd :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl ℝ)
          ((MeasurableEquiv.prodAssoc
            (α := Fin k → ℝ) (β := ℝ)
            (γ := Fin k → ℝ)).symm.trans
              ((MeasurableEquiv.prodCongr
                (MeasurableEquiv.prodComm :
                  (Fin k → ℝ) × ℝ ≃ᵐ ℝ × (Fin k → ℝ))
                (MeasurableEquiv.refl (Fin k → ℝ))).trans
                  (MeasurableEquiv.prodAssoc
                    (α := ℝ) (β := Fin k → ℝ)
                    (γ := Fin k → ℝ)))))
        (volume :
          Measure (ℝ × ((Fin k → ℝ) × (ℝ × (Fin k → ℝ)))))
        (volume :
          Measure (ℝ × (ℝ × ((Fin k → ℝ) × (Fin k → ℝ))))) := by
    simpa using
      (MeasurePreserving.prod
        (MeasurePreserving.id (volume : Measure ℝ)) hInner)
  have hAssoc₄ :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          (ℝ × ℝ) × ((Fin k → ℝ) × (Fin k → ℝ)) ≃ᵐ
            ℝ × (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))).symm
        (volume :
          Measure (ℝ × (ℝ × ((Fin k → ℝ) × (Fin k → ℝ)))))
        (volume :
          Measure ((ℝ × ℝ) × ((Fin k → ℝ) × (Fin k → ℝ)))) := by
    simpa using
      (measurePreserving_prodAssoc
        (volume : Measure ℝ)
        (volume : Measure ℝ)
        (volume : Measure ((Fin k → ℝ) × (Fin k → ℝ)))).symm
  simpa [pairHeadsTailsMeasurableEquiv] using
    hAssoc₁.trans (hProd.trans hAssoc₄)

private theorem osiiMixedHeadTailMeasurableEquiv_measurePreserving
    (k : ℕ) :
    MeasurePreserving
      (osiiMixedHeadTailMeasurableEquiv k)
      (volume : Measure (Fin ((k + 1) + (k + 1)) → ℝ))
      (volume : Measure ((ℝ × ℝ) × (Fin (k + k) → ℝ))) := by
  have hSplit :=
    MeasureTheory.volume_preserving_finAddProd (k + 1) (k + 1) ℝ
  have hHead :=
    MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => ℝ) 0
  have hHeads :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (k + 1) => ℝ) 0)
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (k + 1) => ℝ) 0))
        (volume :
          Measure ((Fin (k + 1) → ℝ) × (Fin (k + 1) → ℝ)))
        (volume :
          Measure ((ℝ × (Fin k → ℝ)) × (ℝ × (Fin k → ℝ)))) := by
    simpa using MeasurePreserving.prod hHead hHead
  have hTail :=
    (MeasureTheory.volume_preserving_finAddProd k k ℝ).symm
  have hTailAppend :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl (ℝ × ℝ))
          (MeasurableEquiv.finAddProd k k ℝ).symm)
        (volume :
          Measure ((ℝ × ℝ) × ((Fin k → ℝ) × (Fin k → ℝ))))
        (volume :
          Measure ((ℝ × ℝ) × (Fin (k + k) → ℝ))) := by
    simpa using
      MeasurePreserving.prod
        (MeasurePreserving.id (volume : Measure (ℝ × ℝ))) hTail
  simpa [osiiMixedHeadTailMeasurableEquiv] using
    hSplit.trans
      (hHeads.trans
        ((pairHeadsTailsMeasurableEquiv_measurePreserving k).trans
          hTailAppend))

theorem integral_osiiMixedHeadTailDelta
    (k : ℕ)
    (F : (Fin ((k + 1) + (k + 1)) → ℝ) → ℂ)
    (hF : Integrable F) :
    (∫ δ, F δ) =
      ∫ tails : Fin (k + k) → ℝ,
        ∫ heads : ℝ × ℝ,
          F (osiiMixedHeadTailDelta heads tails) := by
  let e := osiiMixedHeadTailMeasurableEquiv k
  have hmp := osiiMixedHeadTailMeasurableEquiv_measurePreserving k
  have hcomp :
      (∫ p : (ℝ × ℝ) × (Fin (k + k) → ℝ), F (e.symm p)) =
        ∫ δ, F δ := by
    simpa [e] using hmp.symm.integral_comp' F
  have hcomp_int :
      Integrable
        (fun p : (ℝ × ℝ) × (Fin (k + k) → ℝ) =>
          F (e.symm p)) := by
    simpa [Function.comp_def, e] using
      hmp.symm.integrable_comp_of_integrable hF
  calc
    (∫ δ, F δ) =
        ∫ p : (ℝ × ℝ) × (Fin (k + k) → ℝ), F (e.symm p) :=
      hcomp.symm
    _ =
        ∫ tails : Fin (k + k) → ℝ,
          ∫ heads : ℝ × ℝ, F (e.symm (heads, tails)) := by
      exact integral_prod_symm _ hcomp_int
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with tails
      apply integral_congr_ae
      filter_upwards with heads
      rw [osiiMixedHeadTailMeasurableEquiv_symm_apply]

variable {d k : ℕ} [NeZero d]

/-- A full spatial block with one fixed head-time profile and one coupled
internal-gap profile.  Unlike the reduced product-basepoint representative,
the spatial test is left arbitrary on all `k + 1` particles. -/
noncomputable def headedTimeSpatialFullSource
    (d k : ℕ) [NeZero d]
    (θ : SchwartzMap ℝ ℂ)
    (ψ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    SchwartzNPoint d (k + 1) :=
  section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ
    (SCV.prependField θ ψ)

/-- The fixed-head partial-delta identity with arbitrary full spatial block
tests.  The product-basepoint identity below is the specialization obtained
by applying the normalized spatial basepoint lift to both blocks. -/
theorem
    reflectedMovingSliceScalar_headedTimeSpatial_eq_internalIntegral
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (ψ₁ ψ₂ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ₁ χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (hψ₁ : HasCompactSupport (ψ₁ : (Fin k → ℝ) → ℂ))
    (hψ₂ : HasCompactSupport (ψ₂ : (Fin k → ℝ) → ℂ))
    (z : Fin k → ℂ)
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (headedTimeSpatialFullSource d k θ₁ ψ₁ χ₁)
            (headedTimeSpatialFullSource d k θ₂ ψ₂ χ₂)))
        (reflectedCauchyIncrement z) =
      ∫ tails : Fin (k + k) → ℝ,
        (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails)) *
          osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
            χ₁ χ₂ (reflectedCauchyIncrement z) tails := by
  let η₁ := SCV.prependField θ₁ ψ₁
  let η₂ := SCV.prependField θ₂ ψ₂
  have hη₁ : HasCompactSupport
      (η₁ : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_prependField θ₁ ψ₁ hθ₁ hψ₁
  have hη₂ : HasCompactSupport
      (η₂ : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_prependField θ₂ ψ₂ hθ₂ hψ₂
  change
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (section43OrderedPullbackTimeSpatialTensorCLM
              d (k + 1) χ₁ η₁)
            (section43OrderedPullbackTimeSpatialTensorCLM
              d (k + 1) χ₂ η₂)))
        (reflectedCauchyIncrement z) = _
  rw [
    reflectedMovingSliceScalar_mixed_timeSpatial_eq_blockGlobalIntegral
      A ρ η₁ χ₁ η₂ χ₂ hη₁ hη₂
      (reflectedCauchyIncrement z) hz]
  let F : (Fin ((k + 1) + (k + 1)) → ℝ) → ℂ :=
    fun δ =>
      (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
          η₂ (splitLast (k + 1) (k + 1) δ)) *
        osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
          (reflectedCauchyIncrement z) δ
  have hη₁conj : HasCompactSupport
      (η₁.conj : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_schwartzMap_conj η₁ hη₁
  have hF : Integrable F := by
    simpa [F, SchwartzMap.tensorProduct_apply, zero_add] using
      (integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
        A ρ χ₁ χ₂ η₁.conj η₂ hη₁conj hη₂ hz 0)
  rw [show
      (∫ δ : Fin ((k + 1) + (k + 1)) → ℝ,
          (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
              η₂ (splitLast (k + 1) (k + 1) δ)) *
            osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
              (reflectedCauchyIncrement z) δ) =
        ∫ δ, F δ by rfl]
  rw [integral_osiiMixedHeadTailDelta k F hF]
  apply integral_congr_ae
  filter_upwards with tails
  rw [osiiReflectedMixedProductBasepointKernel]
  calc
    (∫ heads : ℝ × ℝ,
        F (osiiMixedHeadTailDelta heads tails)) =
      ∫ heads : ℝ × ℝ,
        (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails)) *
          ((star (θ₁ heads.1) * θ₂ heads.2) *
            osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
              (reflectedCauchyIncrement z)
              (osiiMixedHeadTailDelta heads tails)) := by
        apply integral_congr_ae
        filter_upwards with heads
        simp only [F, η₁, η₂, SCV.prependField_apply,
          SchwartzMap.conj_apply, osiiMixedHeadTailDelta,
          splitFirst_append, splitLast_append, Fin.cons_zero,
          Fin.cons_succ, map_mul, starRingEnd_apply]
        ring
    _ = _ := by
      simpa using
        (integral_const_mul
          (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails))
          (fun heads : ℝ × ℝ =>
            (star (θ₁ heads.1) * θ₂ heads.2) *
              osiiReflectedMixedMovingKernel A ρ χ₁ χ₂
                (reflectedCauchyIncrement z)
                (osiiMixedHeadTailDelta heads tails)))

theorem
    reflectedMovingSliceScalar_productBasepoint_eq_internalIntegral
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (ψ₁ ψ₂ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ₁ χ₂ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (hψ₁ : HasCompactSupport (ψ₁ : (Fin k → ℝ) → ℂ))
    (hψ₂ : HasCompactSupport (ψ₂ : (Fin k → ℝ) → ℂ))
    (z : Fin k → ℂ)
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (productBasepointSpatialFullSourceCLM
              d k θ₁ ψ₁ χ₁)
            (productBasepointSpatialFullSourceCLM
              d k θ₂ ψ₂ χ₂)))
        (reflectedCauchyIncrement z) =
      ∫ tails : Fin (k + k) → ℝ,
        (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails)) *
          osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
            (section43SpatialBasepointLiftCLM d k
              (normalizedSpatialBasepointCutoff d).toSchwartz χ₁)
            (section43SpatialBasepointLiftCLM d k
              (normalizedSpatialBasepointCutoff d).toSchwartz χ₂)
            (reflectedCauchyIncrement z) tails := by
  let η₁ := SCV.prependField θ₁ ψ₁
  let η₂ := SCV.prependField θ₂ ψ₂
  let ξ₁ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz χ₁
  let ξ₂ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz χ₂
  have hη₁ : HasCompactSupport
      (η₁ : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_prependField θ₁ ψ₁ hθ₁ hψ₁
  have hη₂ : HasCompactSupport
      (η₂ : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_prependField θ₂ ψ₂ hθ₂ hψ₂
  rw [productBasepointSpatialFullSourceCLM_apply,
    productBasepointSpatialFullSourceCLM_apply]
  rw [
    reflectedMovingSliceScalar_mixed_timeSpatial_eq_blockGlobalIntegral
      A ρ η₁ ξ₁ η₂ ξ₂ hη₁ hη₂
      (reflectedCauchyIncrement z) hz]
  let F : (Fin ((k + 1) + (k + 1)) → ℝ) → ℂ :=
    fun δ =>
      (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
          η₂ (splitLast (k + 1) (k + 1) δ)) *
        osiiReflectedMixedMovingKernel A ρ ξ₁ ξ₂
          (reflectedCauchyIncrement z) δ
  have hη₁conj : HasCompactSupport
      (η₁.conj : (Fin (k + 1) → ℝ) → ℂ) :=
    hasCompactSupport_schwartzMap_conj η₁ hη₁
  have hF :
      Integrable F := by
    simpa [F, SchwartzMap.tensorProduct_apply, zero_add] using
      (integrable_tensorProduct_mul_osiiReflectedMixedMovingKernel
        A ρ ξ₁ ξ₂ η₁.conj η₂ hη₁conj hη₂ hz 0)
  rw [show
      (∫ δ : Fin ((k + 1) + (k + 1)) → ℝ,
          (η₁.conj (splitFirst (k + 1) (k + 1) δ) *
              η₂ (splitLast (k + 1) (k + 1) δ)) *
            osiiReflectedMixedMovingKernel A ρ ξ₁ ξ₂
              (reflectedCauchyIncrement z) δ) =
        ∫ δ, F δ by rfl]
  rw [integral_osiiMixedHeadTailDelta k F hF]
  apply integral_congr_ae
  filter_upwards with tails
  rw [osiiReflectedMixedProductBasepointKernel]
  calc
    (∫ heads : ℝ × ℝ,
        F (osiiMixedHeadTailDelta heads tails)) =
      ∫ heads : ℝ × ℝ,
        (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails)) *
          ((star (θ₁ heads.1) * θ₂ heads.2) *
            osiiReflectedMixedMovingKernel A ρ ξ₁ ξ₂
              (reflectedCauchyIncrement z)
              (osiiMixedHeadTailDelta heads tails)) := by
        apply integral_congr_ae
        filter_upwards with heads
        simp only [F, η₁, η₂, SCV.prependField_apply,
          SchwartzMap.conj_apply, osiiMixedHeadTailDelta,
          splitFirst_append, splitLast_append, Fin.cons_zero,
          Fin.cons_succ,
          map_mul, starRingEnd_apply]
        ring
    _ = _ := by
      simpa [ξ₁, ξ₂] using
        (integral_const_mul
          (ψ₁.conj (splitFirst k k tails) *
            ψ₂ (splitLast k k tails))
          (fun heads : ℝ × ℝ =>
            (star (θ₁ heads.1) * θ₂ heads.2) *
              osiiReflectedMixedMovingKernel A ρ ξ₁ ξ₂
                (reflectedCauchyIncrement z)
                (osiiMixedHeadTailDelta heads tails)))

/-- For translated internal approximate identities, arbitrary full spatial
block tests satisfy the same tensor-delta formula. -/
theorem
    reflectedMovingSliceScalar_headedTimeSpatial_translatedApproximateIdentities
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (I J : SchwartzTimeApproximateIdentity k)
    (τ₁ τ₂ : Fin k → ℝ)
    (χ₁ χ₂ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (p q : ℕ)
    (z : Fin k → ℂ)
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (headedTimeSpatialFullSource d k θ₁
              (SCV.translateSchwartz (-τ₁) (I.test p)) χ₁)
            (headedTimeSpatialFullSource d k θ₂
              (SCV.translateSchwartz (-τ₂) (J.test q)) χ₂)))
        (reflectedCauchyIncrement z) =
      ∫ y : Fin (k + k) → ℝ,
        ((I.test p).tensorProduct (J.test q)) y *
          osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
            χ₁ χ₂ (reflectedCauchyIncrement z)
            (Fin.append τ₁ τ₂ + y) := by
  let ψ₁ := SCV.translateSchwartz (-τ₁) (I.test p)
  let ψ₂ := SCV.translateSchwartz (-τ₂) (J.test q)
  rw [
    reflectedMovingSliceScalar_headedTimeSpatial_eq_internalIntegral
      A ρ θ₁ θ₂ ψ₁ ψ₂ χ₁ χ₂ hθ₁ hθ₂
      (hasCompactSupport_translateSchwartz
        (I.test p) (I.compact p) (-τ₁))
      (hasCompactSupport_translateSchwartz
        (J.test q) (J.compact q) (-τ₂))
      z hz]
  let F : (Fin (k + k) → ℝ) → ℂ :=
    fun tails =>
      (ψ₁.conj (splitFirst k k tails) *
          ψ₂ (splitLast k k tails)) *
        osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
          χ₁ χ₂ (reflectedCauchyIncrement z) tails
  calc
    (∫ tails : Fin (k + k) → ℝ, F tails) =
        ∫ y : Fin (k + k) → ℝ,
          F (y + Fin.append τ₁ τ₂) := by
      exact
        (MeasureTheory.integral_add_right_eq_self
          F (Fin.append τ₁ τ₂)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hreal :
          starRingEnd ℂ (I.test p (splitFirst k k y)) =
            I.test p (splitFirst k k y) :=
        Complex.conj_eq_iff_im.mpr
          (I.real p (splitFirst k k y))
      have hψ₁ :
          ψ₁.conj
              (splitFirst k k (y + Fin.append τ₁ τ₂)) =
            I.test p (splitFirst k k y) := by
        simpa [ψ₁, SCV.translateSchwartz_apply,
          SchwartzMap.conj_apply, add_assoc] using hreal
      have hψ₂ :
          ψ₂ (splitLast k k (y + Fin.append τ₁ τ₂)) =
            J.test q (splitLast k k y) := by
        simp [ψ₂, SCV.translateSchwartz_apply, add_assoc]
      simp only [F]
      rw [hψ₁, hψ₂, SchwartzMap.tensorProduct_apply]
      rw [add_comm y (Fin.append τ₁ τ₂)]

/-- For translated internal approximate identities, the product-basepoint
mixed scalar is the tensor smearing of the head-integrated kernel about the
two internal time anchors. -/
theorem
    reflectedMovingSliceScalar_productBasepoint_translatedApproximateIdentities
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (ρ : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (θ₁ θ₂ : SchwartzMap ℝ ℂ)
    (I J : SchwartzTimeApproximateIdentity k)
    (τ₁ τ₂ : Fin k → ℝ)
    (χ₁ χ₂ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hθ₁ : HasCompactSupport (θ₁ : ℝ → ℂ))
    (hθ₂ : HasCompactSupport (θ₂ : ℝ → ℂ))
    (p q : ℕ)
    (z : Fin k → ℂ)
    (hz :
      reflectedCauchyIncrement z ∈
        reflectedMovingSliceCarrier A ρ) :
    reflectedMovingSliceScalar A ρ
        (diffVarReduction d (k + (k + 1))
          (mixedReflectedChronologicalSource
            (productBasepointSpatialFullSourceCLM d k θ₁
              (SCV.translateSchwartz (-τ₁) (I.test p)) χ₁)
            (productBasepointSpatialFullSourceCLM d k θ₂
              (SCV.translateSchwartz (-τ₂) (J.test q)) χ₂)))
        (reflectedCauchyIncrement z) =
      ∫ y : Fin (k + k) → ℝ,
        ((I.test p).tensorProduct (J.test q)) y *
          osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
            (section43SpatialBasepointLiftCLM d k
              (normalizedSpatialBasepointCutoff d).toSchwartz χ₁)
            (section43SpatialBasepointLiftCLM d k
              (normalizedSpatialBasepointCutoff d).toSchwartz χ₂)
            (reflectedCauchyIncrement z)
            (Fin.append τ₁ τ₂ + y) := by
  let ψ₁ := SCV.translateSchwartz (-τ₁) (I.test p)
  let ψ₂ := SCV.translateSchwartz (-τ₂) (J.test q)
  rw [
    reflectedMovingSliceScalar_productBasepoint_eq_internalIntegral
      A ρ θ₁ θ₂ ψ₁ ψ₂ χ₁ χ₂ hθ₁ hθ₂
      (hasCompactSupport_translateSchwartz
        (I.test p) (I.compact p) (-τ₁))
      (hasCompactSupport_translateSchwartz
        (J.test q) (J.compact q) (-τ₂))
      z hz]
  let F : (Fin (k + k) → ℝ) → ℂ :=
    fun tails =>
      (ψ₁.conj (splitFirst k k tails) *
          ψ₂ (splitLast k k tails)) *
        osiiReflectedMixedProductBasepointKernel A ρ θ₁ θ₂
          (section43SpatialBasepointLiftCLM d k
            (normalizedSpatialBasepointCutoff d).toSchwartz χ₁)
          (section43SpatialBasepointLiftCLM d k
            (normalizedSpatialBasepointCutoff d).toSchwartz χ₂)
          (reflectedCauchyIncrement z) tails
  calc
    (∫ tails : Fin (k + k) → ℝ, F tails) =
        ∫ y : Fin (k + k) → ℝ,
          F (y + Fin.append τ₁ τ₂) := by
      exact
        (MeasureTheory.integral_add_right_eq_self
          F (Fin.append τ₁ τ₂)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hreal :
          starRingEnd ℂ (I.test p (splitFirst k k y)) =
            I.test p (splitFirst k k y) :=
        Complex.conj_eq_iff_im.mpr
          (I.real p (splitFirst k k y))
      have hψ₁ :
          ψ₁.conj
              (splitFirst k k (y + Fin.append τ₁ τ₂)) =
            I.test p (splitFirst k k y) := by
        simpa [ψ₁, SCV.translateSchwartz_apply,
          SchwartzMap.conj_apply, add_assoc] using hreal
      have hψ₂ :
          ψ₂ (splitLast k k (y + Fin.append τ₁ τ₂)) =
            J.test q (splitLast k k y) := by
        simp [ψ₂, SCV.translateSchwartz_apply, add_assoc]
      simp only [F]
      rw [hψ₁, hψ₂, SchwartzMap.tensorProduct_apply]
      rw [add_comm y (Fin.append τ₁ τ₂)]

end OSIIChapterV
end OSReconstruction
